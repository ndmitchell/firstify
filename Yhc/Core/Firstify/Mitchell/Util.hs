
module Yhc.Core.Firstify.Mitchell.Util where

import Control.Monad
import Data.Homeomorphic
import Data.List
import qualified Data.Map as Map
import Yhc.Core
import Yhc.Core.UniqueId


instance UniqueId b => UniqueId (a,b) where
    getId (a,b) = getId b
    putId x (a,b) = (a, putId x b)


shellify :: CoreExpr -> Shell CoreExpr1
shellify x = shell (coreExpr1 x) (map shellify $ children x)


-- need to blur all uses and definitions
blurVar :: CoreExpr -> CoreExpr
blurVar = transform f
    where
        f (CoreVar _) = CoreVar ""
        f (CoreLet bind x) = CoreLet (map ((,) "" . snd) bind) x
        f (CoreCase on alts) = CoreCase on [(g a,b) | (a,b) <- alts]
        f (CoreLam x y) = CoreLam (map (const "") x) y
        f x = x

        g (PatCon x _) = PatCon x []
        g x = x


applyFuncBodyCoreM :: Monad m => (CoreFuncName -> CoreExpr -> m CoreExpr) -> Core -> m Core
applyFuncBodyCoreM f = applyFuncCoreM g
    where
        g (CoreFunc name args body) = liftM (CoreFunc name args) $ f name body
        g x = return x


checkFreeVarFuncs :: [CoreFunc] -> Bool
checkFreeVarFuncs funcs = all f funcs && disjoint vars
    where
        vars = concat [v ++ collectBoundVars x | CoreFunc _ v x <- funcs]

        f func@(CoreFunc _ args x) =
            if null (collectFreeVars x \\ args) then True
            else error $ "checkFreeVarCore: " ++ show func
        f x = True


        disjoint x = if null res then True else error $ "not disjoint: " ++ show res
            where res = filter (not . null) . map tail . group . sort $ x


checkFreeVarCoreMap :: CoreFuncMap -> Bool
checkFreeVarCoreMap = checkFreeVarFuncs . Map.elems

checkFreeVarCore :: Core -> Bool
checkFreeVarCore = checkFreeVarFuncs . coreFuncs



-- check a function is confluent
checkConfluent :: Monad m => String -> (Core -> m Core) -> Core -> m Core
checkConfluent name f x = do
    x2 <- f x
    x3 <- f x2
    if x2 == x3
        then return x2
        else do
            let badfunc = head $ concat $ zipWith (\c d -> [coreFuncName c | c /= d])
                                                  (coreFuncs x2) (coreFuncs x3)
                g x = show (coreFunc x badfunc) ++ "\n======\n"
            error $ name ++ ":\n" ++ g x ++ g x2 ++ g x3


applyBodyCoreMapM :: Monad m => (CoreExpr -> m CoreExpr) -> CoreFuncMap -> m CoreFuncMap
applyBodyCoreMapM f x = return . Map.fromAscList =<< mapM g (Map.toAscList x)
    where
        g (n1,CoreFunc n2 args body) = do
            body <- f body
            return (n1, CoreFunc n2 args body)
        g x = return x

