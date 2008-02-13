
module Yhc.Core.Firstify.MitchellOld(mitchellOld) where

import Yhc.Core hiding (uniqueBoundVarsCore, uniqueBoundVars)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Yhc.Core.Firstify.Mitchell.Util
import Yhc.Core.Firstify.Mitchell.Template
import qualified Yhc.Core.Firstify.Mitchell.BiMap as BiMap

import Control.Exception
import Control.Monad
import Control.Monad.State
import qualified Data.Homeomorphic as H
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Debug.Trace
import Safe


logger :: String -> SS a -> SS a
logger x = id


type SS a = State S a

data S = S {inlined :: Set.Set CoreFuncName  -- which have been inlined (termination check)
           ,specialised :: Map.Map CoreFuncName (H.Homeomorphic CoreExpr1 CoreExpr)
                -- ^ which have been specialised within each function (termination check)
           ,special :: BiMap.BiMap CoreFuncName CoreExpr -- which special variants do we have
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use
           }


instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
mitchellOld :: Core -> Core
mitchellOld c = evalState (uniqueBoundVarsCore c2 >>= step) (s0 :: S)
    where
        s0 = S Set.empty Map.empty BiMap.empty 0 (uniqueFuncsNext c2)
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


-- In each step first inline all top-level function bindings
-- and let's that appear to be bound to an unsaturated
--
-- Then specialise each value
step :: Core -> SS Core
step = f acts
    where
        (*) = (,)
        acts = ["lambdas" * lambdas, "simplify" * simplify, "inline" * inline, "specialise" * specialise]

        f [] x = return x
        f ((name,act):ys) x = do
            x2 <- trace name $ act x
            if x == x2 then f ys x else f acts x2


-- make sure every function is given enough arguments, by introducing lambdas
lambdas :: Core -> SS Core
lambdas c2 | checkFreeVarCore c2 = applyBodyCoreM f c
    where
        c = coreReachable ["main"] c2
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

        f (CoreApp (CoreLam vs x) ys) = do
                x2 <- transformExprM f x2
                return $ coreApp (coreLam vs2 x2) ys2
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

        f (CoreLet bind x) | not $ null bad = do
                x <- transformM g x
                x <- transformM f x
                return $ coreLet good x
            where
                (bad,good) = partition (any isCoreLam . universe . snd) bind

                g (CoreVar x) = case lookup x bad of
                                    Nothing -> return $ CoreVar x
                                    Just y -> duplicateExpr y
                g x = return x

        f (CoreCase on@(CoreApp (CoreCon x) xs) alts) | any isCoreLam $ universe on =
                transformM f $ head $ concatMap g alts
            where
                g (PatDefault, y) = [y]
                g (PatCon c vs, y) = [coreLet (zip vs xs) y | c == x]
                g _ = []

        f (CoreCase (CoreCase on alts1) alts2) | any isCoreLam $ concatMap (universe . snd) alts1 =
                transformM f =<< liftM (CoreCase on) (mapM g alts1)
            where
                g (lhs,rhs) = do
                    CoreCase _ alts22 <- duplicateExpr $ CoreCase (CoreLit $ CoreInt 0) alts2
                    return (lhs, CoreCase rhs alts22)

        f (CoreLam vs1 (CoreLam vs2 x)) = return $ CoreLam (vs1++vs2) x
        f (CoreLet bind (CoreLam vs x)) = return $ CoreLam vs (CoreLet bind x)
        f (CoreApp (CoreApp x y) z) = return $ CoreApp x (y++z)

        f x = return x


-- BEFORE: box = [even]
-- AFTER:  all uses of box are inlined
inline :: Core -> SS Core
inline c = do
    s <- get
    let done = inlined s
        todo = Map.fromList [(name,coreLam args body) | CoreFunc name args body <- coreFuncs c
                            ,let b = name `Set.notMember` done, shouldInline body
                            ,if b then True else trace ("Skipped inlining of: " ++ name) False]
    if Map.null todo then return c else 
        logger ("Inlining: " ++ show (Map.keys todo)) $ do
            modify $ \s -> s{inlined = Set.fromList (Map.keys todo) `Set.union` done}
            transformExprM (f todo) c
    where
        f mp (CoreFun x) = case Map.lookup x mp of
                                Nothing -> return $ CoreFun x
                                Just y -> do
                                    y <- duplicateExpr y
                                    transformM (f (Map.delete x mp)) y
        f mp x = return x

        -- should inline if there is a lambda before you get to a function
        shouldInline = any isCoreLam . universe . transform g
        g (CoreApp (CoreFun x) _) = CoreFun x
        g x = x



-- BEFORE: map even x
-- AFTER:  map_even x
specialise :: Core -> SS Core
specialise c = do
        s <- get
        -- new state is a tuple where the first element is a list of new functions
        -- and the second is the existing state
        (c,(new,s)) <- return $ runState (applyFuncCoreM f c) ([],s)
        put s
        return c{coreFuncs = new ++ coreFuncs c}
    where
        f (CoreFunc name args x) = do
            (_,s) <- get
            let homeo = Map.findWithDefault H.empty name (specialised s)
            x <- transformM (g homeo) x
            return $ CoreFunc name args x
        f x = return x

        g homeo x | t /= templateNone = do
                (new,s) <- get
                let tfull = templateExpand (`BiMap.lookup` special s) t
                    th = shellify $ blurVar tfull
                    holes = templateHoles x t
                    prev = H.find th homeo
                case BiMap.lookupRev t (special s) of
                    -- OPTION 1: Not previously done, and a homeomorphic embedding
                    Nothing | length prev > 2 ->
                        trace ("Skipped specialisation of: " ++ show tfull ++
                               "\nBecause of: " ++ show prev) $ return x
                    -- OPTION 2: Previously done and not garbage collected
                    Just name | name `elem` map coreFuncName (new ++ coreFuncs c) -> do
                        return $ coreApp (CoreFun name) holes
                    -- OPTION 3: New todo
                    done -> do
                        let name = uniqueJoin (templateName t) (funcId s)
                        fun <- templateGenerate (coreFunc c{coreFuncs=new++coreFuncs c}) name t
                        modify $ \(new,s) -> (fun : new,
                             s{specialised = Map.insert name (H.insert th t homeo) (specialised s)
                              ,funcId = funcId s + 1
                              ,special = BiMap.insert name t (special s)
                              })
                        return $ {-  trace
                            ("Specialising as " ++ name ++ " " ++ show tfull) $ -}
                            coreApp (CoreFun name) holes
            where t = templateCreate x

        g homeo x = return x
