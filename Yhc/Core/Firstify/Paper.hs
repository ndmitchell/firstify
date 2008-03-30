
module Yhc.Core.Firstify.Paper(paper) where

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
import qualified Data.Set as Set
import Data.List
import Data.Maybe
import Debug.Trace
import Safe



type SS a = State S a

data S = S {terminate :: Terminate -- termination check
           ,special :: BiMap.BiMap CoreFuncName Template -- which special variants do we have
           ,coreRest :: Core -- the functions are not there
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use

           -- used only in the individual step
           ,funS :: FunS
           }


data FunS = FunS
    {sBox :: [CoreFuncName]
    ,sArity :: [(CoreFuncName,Int)]
    ,sTemplate :: [Template]
    }
emptyFunS = FunS [] [] []


data Info = Info
    {iBox :: Set.Set CoreFuncName
    ,iArity :: Map.Map CoreFuncName Int
    ,iFunS :: Map.Map CoreFuncName FunS
    }


instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
paper :: Core -> Core
paper c = fromCoreFuncMap c2 res
    where
        res = evalState (liftM toCoreFuncMap (uniqueBoundVarsCore c2) >>= run) (s0 :: S)
        s0 = S (emptyTerminate True) BiMap.empty c2 0 (uniqueFuncsNext c2) emptyFunS
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


run :: CoreFuncMap -> SS CoreFuncMap
run precore = step i False core orde
    where
        i = Info (boxApprox core orde) (Map.map coreFuncArity core) Map.empty
        core = Map.map (applyBodyFunc wrapCoreFun) precore
        orde = order core


-- return True if they agree
checkStat :: Info -> FunS -> Bool
checkStat i s = all (`Set.notMember` (iBox i)) (sBox s) &&
                all (\(n,a) -> a == (iArity i Map.! n)) (sArity s)


step :: Info -> Bool -> CoreFuncMap -> [CoreFuncName] -> SS CoreFuncMap
step i chng core (t:odo) 
    | maybe True (not . checkStat i) $ Map.lookup t (iFunS i)
    = do
    modify $ \s -> s{funS = emptyFunS}
    fun <- func arity boxed (inline core) (template core) (core Map.! t)
    let a = coreFuncArity fun
    b <- isBox boxed (coreFuncBody fun)
    let c = a /= iArity i Map.! t ||
            b /= t `Set.member` iBox i
    s <- get
    i <- return $ Info {iBox = (if b then Set.insert t else id) (iBox i)
                       ,iArity = Map.insert t a (iArity i)
                       ,iFunS = Map.insert t (funS s) (iFunS i)
                       }
    core <- return $ Map.insert t fun core
    step i (chng || c) core odo
    where
        arity name = do
            let res = iArity i Map.! name
            modifyS $ \s -> s{sArity = (name,res) : sArity s}
            return res

        boxed name = do
            let res = name `Set.member` iBox i
            when (not res) $ modifyS $ \s -> s{sBox = name : sBox s}
            return res

        modifyS f = modify $ \s -> s{funS = f (funS s)}

step i chng core (t:odo) = step i chng core odo

step i False core [] = return core
step i True core [] = step i False core (order core)


-- which order should we do this in
-- should be main last, all its dependencies before
-- but skip anything unreachable
order :: CoreFuncMap -> [CoreFuncName]
order core = [name | CoreFunc name _ _ <- Map.elems core]


-- make an approximation of which functions are boxes at the start
-- also use the initial ordering, to give you a hand
boxApprox :: CoreFuncMap -> [CoreFuncName] -> Set.Set CoreFuncName
boxApprox _ _ = Set.empty



wrapCoreFun (CoreFun x) = CoreApp (CoreFun x) []
wrapCoreFun (CoreApp x y) = CoreApp (descend wrapCoreFun x) (map wrapCoreFun y)
wrapCoreFun x = descend wrapCoreFun x



isBox :: (CoreFuncName -> SS Bool) -> CoreExpr -> SS Bool
isBox f (CoreApp (CoreCon _) xs) = return (any isCoreLam xs) `orM` anyM (isBox f) xs
isBox f (CoreLet _ x) = isBox f x
isBox f (CoreApp (CoreFun x) _) = f x
isBox f (CoreCase _ xs) = anyM (isBox f . snd) xs
isBox f _ = return False


orM a b = do a <- a; if a then return True else b
orsM [] = return False
orsM (x:xs) = orM x (orsM xs)
anyM f = orsM . map f

partitionM f [] = return ([],[])
partitionM f (x:xs) = do
    t <- f x
    (a,b) <- partitionM f xs
    return (if t then x:a else a, if t then b else x:b)


-- run over a function
func :: (CoreFuncName -> SS Int) -> (CoreFuncName -> SS Bool) ->
        (CoreFuncName -> SS (Maybe CoreExpr)) -> (CoreFuncName -> [CoreExpr] -> SS CoreExpr) ->
        CoreFunc -> SS CoreFunc
func arity boxed inline template (CoreFunc name args body) = do
    (args2,body2) <- liftM fromCoreLam $ transformM f body
    return $ CoreFunc name (args++args2) body2
    where
        -- ARITY RAISING RULE
        -- SPECIALISE RULE
        f (CoreApp (CoreFun x) xs) = do
            a <- arity x
            let extra = a - length xs
            if extra <= 0
                then template x xs
                else do
                    vs <- getVars extra
                    let xs2 = xs ++ map CoreVar vs
                    f . CoreLam vs =<< template x xs2

        -- INLINE RULE
        f o@(CoreCase (CoreApp (CoreFun x) xs) alts) = do
            b <- boxed x
            if not b then return o else do
                x2 <- inline x
                case x2 of
                    Nothing -> return o
                    Just y -> do
                        on <- f $ CoreApp y xs
                        f $ CoreCase on alts

        -- SIMPLIFY RULES
        f (CoreApp (CoreLam vs x) ys) = do
                x2 <- transformExprM f x2
                return $ coreApp (coreLam vs2 x2) ys2
            where
                i = min (length vs) (length ys)
                (vs1,vs2) = splitAt i vs
                (ys1,ys2) = splitAt i ys
                (rep,bind) = partition (\(a,b) -> isCoreVar b || countFreeVar a x <= 1) (zip vs1 ys1)
                x2 = coreLet bind $ replaceFreeVars rep x

        f (CoreCase (CoreLet bind on) alts) = do
            cas <- f $ CoreCase on alts
            f $ CoreLet bind cas

        f (CoreCase on alts) | not $ null ar = do
                vs <- getVars $ maximum ar
                let vs2 = map CoreVar vs
                alts <- sequence [liftM ((,) a) $ f $ CoreApp b vs2 | (a,b) <- alts]
                return $ CoreLam vs $ CoreCase on alts
            where
                ar = [length vs | (_, CoreLam vs x) <- alts]

        f (CoreCase on@(CoreApp (CoreCon x) xs) alts) =
                (if null xs then return else f) $ head $ concatMap g alts
            where
                g (PatDefault, y) = [y]
                g (PatCon c vs, y) = [coreLet (zip vs xs) y | c == x]
                g _ = []

        f (CoreCase (CoreCase on alts1) alts2) =
                f =<< liftM (CoreCase on) (mapM g alts1)
            where
                g (lhs,rhs) = do
                    CoreCase _ alts22 <- duplicateExpr $ CoreCase (CoreLit $ CoreInt 0) alts2
                    rhs <- f $ CoreCase rhs alts22
                    return (lhs, rhs)

        f (CoreLam vs1 (CoreLam vs2 x)) = return $ CoreLam (vs1++vs2) x
        f (CoreLet bind (CoreLam vs x)) = liftM (CoreLam vs) $ f (CoreLet bind x)
        f (CoreApp (CoreApp x y) z) = return $ CoreApp x (y++z)

        f (CoreLet bind x) = do
                (bad,good) <- partitionM (\(a,b) -> return (isCoreLam b) `orM` isBox boxed b) bind
                if null bad
                    then return $ CoreLet bind x
                    else liftM (coreLet good) $ transformM (g bad) x
            where
                g bad (CoreVar x) = case lookup x bad of
                                    Nothing -> return $ CoreVar x
                                    Just y -> duplicateExpr y
                g bad x = f x

        f x = return x


inline :: CoreFuncMap -> CoreFuncName -> SS (Maybe CoreExpr)
inline core name = do
    let CoreFunc _ args body = core Map.! name
    liftM Just $ duplicateExpr $ coreLam args body


template :: CoreFuncMap -> CoreFuncName -> [CoreExpr] -> SS CoreExpr
template core name args = return $ CoreApp (CoreFun name) args

