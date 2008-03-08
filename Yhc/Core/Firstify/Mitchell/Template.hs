
module Yhc.Core.Firstify.Mitchell.Template where

import Control.Monad.State
import Data.List
import Debug.Trace
import Yhc.Core hiding (uniqueBoundVarsCore, uniqueBoundVars)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId
import Yhc.Core.Util


-- all templates must be at least: CoreApp (CoreFun _) _
type Template = CoreExpr

templateNone :: Template
templateNone = CoreVar "_"


-- given an expression, what would be the matching template
-- must be careful to avoid if there is an inner template not redoing it
templateCreate :: (CoreFuncName -> Bool) -> CoreExpr -> Template
templateCreate isPrim o@(CoreApp (CoreFun x) xs)
        | any ((/=) templateNone . templateCheck) $ tail $ universe o = templateNone
        | isPrim x && res /= templateNone = trace ("Warning: primitive HO call, " ++ x) templateNone
        | otherwise = res
    where
        res = templateCheck o

templateCreate _ _ = templateNone


templateCheck :: CoreExpr -> Template
templateCheck o@(CoreApp (CoreFun x) xs) = flip evalState (1 :: Int) $
        uniqueBoundVars $ join (CoreApp (CoreFun x)) (map f xs)
    where
        free = collectFreeVars o
        f (CoreLam vs x) = CoreLam vs (f x)
        f (CoreVar x) = if x `elem` free then templateNone else CoreVar x
        f (CoreApp x xs) | isCoreCon x || isCoreFun x = join (CoreApp x) (map f xs)
        f x = join generate (map f children)
            where (children,generate) = uniplate x

        join g xs | any (/= templateNone) xs = g xs
                  | otherwise = templateNone

templateCheck _ = templateNone



-- pick a human readable name for a template result
templateName :: Template -> String
templateName (CoreApp (CoreFun name) xs) = concat $ intersperse "_" $ map short $ name :
    [x | CoreFun x <- map (fst . fromCoreApp . snd . fromCoreLam) xs, '_' `notElem` x]
    where short = reverse . takeWhile (/= ';') . reverse
templateName _ = "template"


-- for each CoreVar "_", get the associated expression
templateHoles :: CoreExpr -> Template -> [CoreExpr]
templateHoles x y | y == templateNone = [x]
                  | otherwise = concat $ zipWith templateHoles (children x) (children y)


templateExpand :: (CoreFuncName -> Maybe Template) -> Template -> Template
templateExpand mp = transform f
    where
        f (CoreFun x) = case mp x of
                            Just y -> transform f y
                            Nothing -> CoreFun x
        f x = x


templateGenerate :: UniqueIdM m => (CoreFuncName -> CoreFunc) -> CoreFuncName -> Template -> m CoreFunc
templateGenerate ask newname o@(CoreApp (CoreFun name) xs) = do
    let fun = ask name
        CoreFunc _ args body | isCoreFunc fun = fun
            | otherwise = error $ "Tried specialising on a primitve: " ++ show o
    x <- duplicateExpr $ coreLam args body
    xs <- mapM duplicateExpr xs
    count1 <- getIdM
    xs <- mapM (transformM f) xs
    count2 <- getIdM
    putIdM count1
    vs <- getVars (count2-count1)
    return $ CoreFunc newname vs (coreApp x xs)
    where
        f x | x == templateNone = liftM CoreVar getVar
        f x = return x


-- given an expand function, and an existing template, and a new template
-- return a new template, based on the original, but only if there is an embedding
templateWeaken :: (Template -> Template) -> Template -> Template -> Template
templateWeaken expand bad new = f new
    where
        bad2 = blurVar bad
        free = collectFreeVars new

        f x = if blurVar (expand x) == bad2 && null (collectFreeVars x \\ free)
              then templateNone
              else descend f x
