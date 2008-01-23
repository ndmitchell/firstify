
module Yhc.Core.Firstify.Mitchell(mitchell) where

import Yhc.Core hiding (uniqueBoundVarsCore)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Control.Monad
import Control.Monad.State
import qualified Data.Homeomorphic as H
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List
import Debug.Trace


logger :: String -> SS a -> SS a
logger x = id


type SS a = State S a

data S = S {inlined :: Set.Set CoreFuncName  -- which have been inlined (termination check)
           ,specialised :: H.Homeomorphic CoreExpr1 () -- which have been specialised (termination check)
           ,special :: Map.Map CoreExpr CoreFuncName -- which special variants do we have (CoreVar "" is wildcard)
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use
           }


instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
mitchell :: Core -> Core
mitchell c = evalState (step =<< uniqueBoundVarsCore c2) s0
    where
        s0 = S Set.empty H.empty Map.empty 0 (uniqueFuncsNext c2)
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


fixM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixM f x = do
    x2 <- f x
    if x == x2 then return x2 else fixM f x2 


-- In each step first inline all top-level function bindings
-- and let's that appear to be bound to an unsaturated
--
-- Then specialise each value
step :: Core -> SS Core
step = ("lambdas",lambdas) * ("simplify",simplify) -- * inline
    where
        -- assume 'a' finds a fixed point on its own
        (*) a b x = do
            let ap (name,func) x = trace name $ checkConfluent name func x
            x2 <- ap a x
            x3 <- ap b x2
            if x3 == x2 then return x2 else (*) a b x3


diagnose msg a b = head [error $ msg ++ ":\n" ++ show c ++ "\n======\n" ++ show d
                        | (c,d) <- zip (coreFuncs a) (coreFuncs b), c /= d]


-- check a function is confluent
checkConfluent :: String -> (Core -> SS Core) -> Core -> SS Core
checkConfluent name f x = do
    x2 <- f x
    x3 <- f x2
    if x2 == x3
        then return x2
        else diagnose name x2 x3


applyBodyCoreM f c = do
    res <- mapM g (coreFuncs c)
    return $ c{coreFuncs = res}
    where
        g (CoreFunc a b c) = liftM (CoreFunc a b) $ f c
        g x = return x


-- make sure every function is given enough arguments, by introducing lambdas
lambdas :: Core -> SS Core
lambdas c = applyBodyCoreM f c
    where
        arr = (Map.!) $ Map.fromList [(coreFuncName x, coreFuncArity x) | x <- coreFuncs c]

        f o@(CoreApp (CoreFun x) xs) = do
            xs <- mapM f xs
            let extra = arr x - length xs
            if extra <= 0 then return $ coreApp (CoreFun x) xs else do
                vs <- getVars (arr x)
                return $ coreApp (coreLam vs (coreApp (CoreFun x) (map CoreVar vs))) xs

        f (CoreFun x) = f $ CoreApp (CoreFun x) []
        f x = descendM f x


-- perform basic simplification to remove lambda's
-- basic idea is to lift lambda's outwards to the top
simplify :: Core -> SS Core
simplify c = return . applyFuncCore g =<< transformExprM f c
    where
        g (CoreFunc name args (CoreLam vars body)) = CoreFunc name (args++vars) body
        g x = x

        f (CoreApp (CoreLam vs x) ys) = return $ coreApp (coreLam vs2 x2) ys2
            where
                i = min (length vs) (length ys)
                (vs1,vs2) = splitAt i vs
                (ys1,ys2) = splitAt i ys
                (rep,bind) = partition (\(a,b) -> isCoreVar b || countFreeVar a x <= 1) (zip vs1 ys1)
                x2 = coreLet bind $ replaceFreeVars rep x

        f (CoreCase on alts) | not $ null ar = do
                vs <- getVars $ maximum ar
                transformExprM f $ CoreLam vs $ CoreCase on
                    [(a, CoreApp b (map CoreVar vs)) | (a,b) <- alts]
            where
                ar = [length vs | (_, CoreLam vs x) <- alts]

        f (CoreLam vs1 (CoreLam vs2 x)) = return $ CoreLam (vs1++vs2) x
        f x = return x


-- BEFORE: box = [even]
-- AFTER:  all uses of box are inlined
inline :: Core -> SS Core
inline c = do
    s <- get
    let done = inlined s
        todo = Map.fromList [(name,coreLam args body) | CoreFunc name args body <- coreFuncs c
                            , name `Set.notMember` done, shouldInline body]
    if Map.null todo then return c else 
        logger ("Inlining: " ++ show (Map.keys todo)) $ do
            modify $ \s -> s{inlined = Set.fromList (Map.keys todo) `Set.union` done}
            transformExprM (f (`Map.lookup` todo)) c
    where
        f mp (CoreFun x) = case mp x of
                                Nothing -> return $ CoreFun x
                                Just y -> do
                                    y <- duplicateExpr y
                                    return y
        f mp x = return x

        shouldInline (CoreApp (CoreCon x) xs) = any shouldInline xs
        shouldInline (CoreLam _ _) = True
        shouldInline _ = False



-- BEFORE: map even x
-- AFTER:  map_even x
specialise :: Core -> SS Core
specialise c = return c
