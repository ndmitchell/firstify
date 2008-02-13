
module Yhc.Core.Firstify.Mitchell.Template where

import Control.Monad.State
import Data.List
import Yhc.Core hiding (uniqueBoundVarsCore, uniqueBoundVars)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId


-- all templates must be at least: CoreApp (CoreFun _) _
type Template = CoreExpr

templateNone :: Template
templateNone = CoreVar "_"


-- given an expression, what would be the matching template
-- assume template is called in a bottom-up manner, so
-- can ignore the effect of multiple templatings
templateCreate :: CoreExpr -> Template
templateCreate o@(CoreApp (CoreFun x) xs) = flip evalState (1 :: Int) $
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

templateCreate _ = templateNone


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
