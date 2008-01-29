
module Yhc.Core.Firstify.Mitchell.Util where

import Data.Homeomorphic
import Data.List
import Yhc.Core


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


checkFreeVarCore :: Core -> Bool
checkFreeVarCore c = all f (coreFuncs c) && disjoint vars
    where
        vars = concat [v ++ collectBoundVars x | CoreFunc _ v x <- coreFuncs c]

        f func@(CoreFunc _ args x) =
            if null (collectFreeVars x \\ args) then True
            else error $ "checkFreeVarCore: " ++ show func
        f x = True


        disjoint x = if null res then True else error $ "not disjoint: " ++ show res
            where res = filter (not . null) . map tail . group . sort $ x
