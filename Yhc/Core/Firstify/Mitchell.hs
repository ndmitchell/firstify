
module Yhc.Core.Firstify.Mitchell(mitchell) where

import Yhc.Core hiding (uniqueBoundVarsCore, uniqueBoundVars)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Yhc.Core.Util
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
                (bad,good) = partition (any h . universe . snd) bind

                h (CoreFun x) | isCoreFunc res && boxedLambda (coreFuncBody res) = True
                    where res = c Map.! x 
                h x = isCoreLam x

                g (CoreVar x) = case lookup x bad of
                                    Nothing -> return $ CoreVar x
                                    Just y -> duplicateExpr y
                g x = return x

        f (CoreCase on@(CoreApp (CoreCon x) xs) alts) =
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
--         foo = box
-- AFTER: all uses of box as a case scrutinee are inlined
--        all uses of foo are inlined
inline :: CoreFuncMap -> SS CoreFuncMap
inline c = do
    s <- get
    let boxy = Map.fromList [(name,(True, coreLam args body)) | CoreFunc name args body <- Map.elems c
                            ,boxedLambda body]
        fwd  = Map.fromList [(name,(False,coreLam args body)) | CoreFunc name args body <- Map.elems c
                            ,Just x <- [simpleForward body], x `Map.member` boxy]
        both = Map.union boxy fwd
    if Map.null both
        then return c
        else applyFuncBodyCoreMapM (\name -> transformM (f (terminate s) both name)) c
    where
        f term both within o = case o of
            CoreCase (CoreFun x) alts -> f term both within $ CoreCase (CoreApp (CoreFun x) []) alts
            CoreCase (CoreApp (CoreFun x) xs) alts | test x True -> do
                res <- inline x
                return $ CoreCase (coreApp res xs) alts
            CoreCase (CoreApp (CoreFun x) []) alts -> return $ CoreCase (CoreFun x) alts
            CoreFun x | test x False -> inline x
            _ -> return o
            where
                test x b = maybe False ((==) b . fst) $ Map.lookup x both

                inline name | askInline within name term = do
                    modify $ \s -> s{terminate = addInline within name (terminate s)}
                    y <- duplicateExpr $ snd $ both Map.! name
                    -- try and inline in the context of the person you are grabbing from
                    transformM (f term (Map.delete name both) name) y
                inline name = return $ CoreFun name


-- is a boxed lambda if there is a lambda before you get to a function
-- assume simplify/promote/lambda have all been fixed pointed
boxedLambda :: CoreExpr -> Bool
boxedLambda = any isCoreLam . universe . transform f
    where
        f (CoreApp (CoreFun x) _) = CoreFun x
        f x = x


-- is this function an absolutely trivialy forwarder
simpleForward :: CoreExpr -> Maybe CoreFuncName
simpleForward (CoreFun x) = Just x
simpleForward (CoreLet _ x) = simpleForward x
simpleForward (CoreApp x _) = simpleForward x
simpleForward _ = Nothing


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
        isPrim x = maybe False isCorePrim $ Map.lookup x c
        isBoxy x = not (isPrim x) && maybe False (boxedLambda . coreFuncBody) (Map.lookup x c)

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
                             s{terminate = cloneSpec within name
                                         $ addSpec within tfull
                                         $ terminate s
                              ,funcId = funcId s + 1
                              ,special = BiMap.insert name t (special s)
                              })
                        return $ coreApp (CoreFun name) holes
            where t = templateCreate isPrim isBoxy x

        f name x = return x
