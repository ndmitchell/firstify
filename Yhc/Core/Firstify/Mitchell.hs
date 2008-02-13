
module Yhc.Core.Firstify.Mitchell(mitchell) where

import Yhc.Core hiding (uniqueBoundVarsCore, uniqueBoundVars)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Yhc.Core.Firstify.Mitchell.Util
import Yhc.Core.Firstify.Mitchell.Template
import Yhc.Core.Firstify.Mitchell.Terminate
import qualified Yhc.Core.Firstify.Mitchell.BiMap as BiMap

import Control.Exception
import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Debug.Trace
import Safe


logger :: String -> SS a -> SS a
logger x = id


type SS a = State S a

data S = S {terminate :: Terminate -- termination check
           ,special :: BiMap.BiMap CoreFuncName CoreExpr -- which special variants do we have
           ,suspend :: CoreFuncMap
           ,coreRest :: Core -- the functions are not there
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use
           }


instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
mitchell :: Core -> Core
mitchell c = fromCoreFuncMap c2 res
    where
        res = evalState (liftM toCoreFuncMap (uniqueBoundVarsCore c2) >>= step) (s0 :: S)
        s0 = S (emptyTerminate True) BiMap.empty Map.empty c2 0 (uniqueFuncsNext c2)
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


-- In each step first inline all top-level function bindings
-- and let's that appear to be bound to an unsaturated
--
-- Then specialise each value
step :: CoreFuncMap -> SS CoreFuncMap
step = f acts
    where
        (*) = (,)
        acts = ["lambdas" * lambdas, "simplify" * simplify, "inline" * inline, "specialise" * specialise]

        f [] x = return x
        f ((name,act):ys) x = do
            x2 <- trace name $ act x
            if x == x2 then f ys x else f acts x2


-- make sure every function is given enough arguments, by introducing lambdas
lambdas :: CoreFuncMap -> SS CoreFuncMap
lambdas c | checkFreeVarCoreMap c = do
        s <- get
        let funcs = c `Map.union` suspend s
            alive = coreReachableMap ["main"] funcs
        put $ s{suspend = Map.filterWithKey (\key _ -> key `Map.notMember` alive) funcs}
        applyBodyCoreMapM (f alive) alive
    where
        f alive o@(CoreApp (CoreFun x) xs) = do
            xs <- mapM (f alive) xs
            let arity = coreFuncArity $ alive Map.! x
                extra = arity - length xs
            if extra <= 0 then return $ coreApp (CoreFun x) xs else do
                vs <- getVars arity
                return $ coreApp (coreLam vs (coreApp (CoreFun x) (map CoreVar vs))) xs

        f alive (CoreFun x) = f alive $ CoreApp (CoreFun x) []
        f alive x = descendM (f alive) x


-- perform basic simplification to remove lambda's
-- basic idea is to lift lambda's outwards to the top
simplify :: CoreFuncMap -> SS CoreFuncMap
simplify c = return . applyFuncCoreMap g =<< transformExprM f c
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
inline :: CoreFuncMap -> SS CoreFuncMap
inline c = do
    s <- get
    let todo = Map.fromList [(name,coreLam args body) | CoreFunc name args body <- Map.elems c
                            ,shouldInline body]
    if Map.null todo
        then return c
        else applyFuncBodyCoreMapM (\name -> transformM (f (terminate s) todo name)) c
    where
        -- note: deliberately use term from BEFORE this state
        -- so you keep inlining many times per call
        f term mp name (CoreFun x)
            | x `Map.member` mp && askInline name x term
            = do modify $ \s -> s{terminate = addInline name x (terminate s)}
                 y <- duplicateExpr $ mp Map.! x
                 -- try and inline in the context of the person you are grabbing from
                 transformM (f term (Map.delete x mp) x) y

        f term mp name x = return x


        -- should inline if there is a lambda before you get to a function
        shouldInline = any isCoreLam . universe . transform g
        g (CoreApp (CoreFun x) _) = CoreFun x
        g x = x



-- BEFORE: map even x
-- AFTER:  map_even x
specialise :: CoreFuncMap -> SS CoreFuncMap
specialise c = do
        s <- get
        (c,(new,s)) <- return $ flip runState (Map.empty,s) $
            applyFuncBodyCoreMapM (\name -> transformM (f name)) c
        put s
        return $ c `Map.union` new
    where
        f within x | t /= templateNone = do
                (new,s) <- get
                let tfull = templateExpand (`BiMap.lookup` special s) t
                    holes = templateHoles x t
                case BiMap.lookupRev t (special s) of
                    -- OPTION 1: Not previously done, and a homeomorphic embedding
                    Nothing | not $ askSpec within tfull (terminate s) -> return x
                    -- OPTION 2: Previously done
                    Just name ->
                        return $ coreApp (CoreFun name) holes
                    -- OPTION 3: New todo
                    done -> do
                        let name = uniqueJoin (templateName t) (funcId s)
                            findCoreFunc name = Map.findWithDefault (new Map.! name) name c
                        fun <- templateGenerate findCoreFunc name t
                        modify $ \(new,s) -> (Map.insert name fun new,
                             s{terminate = addSpec name tfull $
                                           cloneSpec within name $ terminate s
                              ,funcId = funcId s + 1
                              ,special = BiMap.insert name t (special s)
                              })
                        return $ coreApp (CoreFun name) holes
            where t = templateCreate x

        f name x = return x
