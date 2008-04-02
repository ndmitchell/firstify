
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

type BoxesSet = Set.Set CoreFuncName

data S = S {terminate :: Terminate -- termination check
           ,special :: BiMap.BiMap CoreFuncName Template -- which special variants do we have
           ,coreRest :: Core -- the functions are not there
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use

           -- used in the algorithm steps
           ,boxes :: BoxesSet
           ,core :: CoreFuncMap
           -- used for global algorithm control
           ,stack :: Map.Map CoreFuncName Bool -- True is on the stack, False is done
           ,assume :: [(CoreFuncName,Bool,Int)] -- what you assumed
           -- used for local algorithm control
           ,templated :: Bool
           }

instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
paper :: Core -> Core
paper c = fromCoreFuncMap c2 $ coreReachableMap ["main"] res
    where
        res = evalState (liftM toCoreFuncMap (uniqueBoundVarsCore c2) >>= run) (s0 :: S)
        s0 = S (emptyTerminate True) BiMap.empty c2 0 (uniqueFuncsNext c2)
               undefined undefined undefined undefined undefined
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


run :: CoreFuncMap -> SS CoreFuncMap
run precore = do
    cr <- etaRaise precore
    modify $ \s -> s{core=cr, boxes=boxApprox cr}
    step
    liftM core get


-- need to return assumptions made
--      (name :: CoreFuncName, box :: Bool, arity :: Int)
-- need to track which functions are on the stack (Just True), and which
-- have been done (Just False)
step :: SS ()
step = do
    () <- trace "Iterating" $ return ()
    modify $ \s -> s{stack=Map.empty, assume=[]}
    go "main"
    s <- get
    let check (name,b,a) = sArity s name == a && sBoxed s name == b
    if all check (assume s) then return () else step
    where

    -- make sure the name has been optimised already
    go name = do
        s <- get
        case Map.lookup name (stack s) of
            Just False -> return ()
            Just True -> modify $ \s -> s{assume=(name,sBoxed s name,sArity s name):assume s}
            Nothing -> let fun = core s Map.! name in
                if isCorePrim fun then do
                    modify $ \s -> s{stack = Map.insert name False (stack s)}
                 else do
                    modify $ \s -> s{stack = Map.insert name True (stack s)}
                    fun <- func fun
                    fun <- goes fun
                    modify $ \s -> s
                        {boxes = if not (sBoxed s name) && isBox (sBoxed s) (coreFuncBody fun)
                                 then Set.insert name (boxes s) else boxes s
                        ,core = Map.insert name fun (core s)
                        ,stack = Map.insert name False (stack s)}

    goes fun = do
        mapM go [x | CoreFun x <- universe $ coreFuncBody fun]
        modify $ \s -> s{templated = False}
        fun <- func fun
        s <- get
        if templated s then goes fun else return fun




sArity s name = coreFuncArity (core s Map.! name)
sBoxed s name = name `Set.member` boxes s


-- two steps:
-- 1) etaRaise a function if you can
-- 2) ensure all CoreFun's are wrapped in CoreApp's
etaRaise :: CoreFuncMap -> SS CoreFuncMap
etaRaise core = liftM Map.fromAscList $ mapM f $ Map.toAscList core
    where
        f (nam1,CoreFunc nam2 args body) = do
            body <- g body
            return (nam1, CoreFunc nam2 args body)
        f x = return x

        g (CoreFun x) = h x []
        g (CoreApp (CoreFun x) xs) = h x =<< mapM g xs
        g x = descendM g x

        h x xs = do
            let ar = coreFuncArity $ core Map.! x
                nxs = length xs
            if ar <= nxs
                then return $ CoreApp (CoreFun x) xs
                else do
                    vs <- getVars (ar - nxs)
                    return $ CoreLam vs (CoreApp (CoreFun x) (xs ++ map CoreVar vs))


type SetBoxes = Set.Set CoreFuncName


-- for each function, store a Bool saying if you are a box or not
boxApprox :: CoreFuncMap -> SetBoxes
boxApprox core = Set.fromAscList [a | (a,True) <- Map.toAscList $ f Map.empty "main"]
    where
        f res x | x `Map.member` res = res
                | isCorePrim fun = Map.insert x False res
                | otherwise = Map.insert x (isBox (res2 Map.!) bod) res2
            where
                -- important, initially assume always not a box, then refine
                res2 = foldl f (Map.insert x False res) calls
                calls = [x | CoreFun x <- universe bod]
                bod = coreFuncBody fun
                fun = core Map.! x



isBox :: (CoreFuncName -> Bool) -> CoreExpr -> Bool
isBox f (CoreApp (CoreCon _) xs) = any isCoreLam xs || any (isBox f) xs
isBox f (CoreLet _ x) = isBox f x
isBox f (CoreApp (CoreFun x) _) = f x
isBox f (CoreCase _ xs) = any (isBox f . snd) xs
isBox f _ = False



-- run over a function
func :: CoreFunc -> SS CoreFunc
func (CoreFunc name args body) = do
    (args2,body2) <- liftM fromCoreLam $ transformM f body
    return $ CoreFunc name (args++args2) body2
    where
        -- ARITY RAISING RULE
        -- SPECIALISE RULE
        f (CoreApp (CoreFun x) xs) = do
            s <- get
            let a = sArity s x
                extra = a - length xs
            if extra <= 0
                then template x xs
                else do
                    vs <- getVars extra
                    let xs2 = xs ++ map CoreVar vs
                    f . CoreLam vs =<< template x xs2

        -- must go before the inline rule, or gets overlapped
        f (CoreCase on alts) | not $ null ar = do
                vs <- getVars $ maximum ar
                let vs2 = map CoreVar vs
                alts <- sequence [liftM ((,) a) $ f $ CoreApp b vs2 | (a,b) <- alts]
                f . CoreLam vs =<< f (CoreCase on alts)
            where
                ar = [length vs | (_, CoreLam vs x) <- alts]

        -- INLINE RULE
        f o@(CoreCase (CoreApp (CoreFun x) xs) alts) = do
            s <- get
            let b = sBoxed s x
            if not b then return o else do
                x2 <- inline x
                on <- f $ CoreApp x2 xs
                f $ CoreCase on alts

        f (CoreCase (CoreFun x) _) = error "unwrapped fun"

        -- SIMPLIFY RULES
        f (CoreApp (CoreLam vs x) ys) = do
                transformM f $ coreApp (coreLam vs2 x2) ys2
            where
                i = min (length vs) (length ys)
                (vs1,vs2) = splitAt i vs
                (ys1,ys2) = splitAt i ys
                (rep,bind) = partition (\(a,b) -> isCoreVar b || countFreeVar a x <= 1) (zip vs1 ys1)
                x2 = coreLet bind $ replaceFreeVars rep x

        f (CoreCase (CoreLet bind on) alts) = do
            cas <- f $ CoreCase on alts
            f $ CoreLet bind cas

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
        f (CoreLet bind (CoreLam vs x)) = f . CoreLam vs =<< f (CoreLet bind x)
        f (CoreApp (CoreApp x y) z) = return $ CoreApp x (y++z)

        f (CoreLet bind x) = do
                s <- get
                let (bad,good) = partition (\(a,b) -> isCoreLam b || isBox (sBoxed s) b) bind
                if null bad
                    then return $ CoreLet bind x
                    else transformM f =<< liftM (coreLet good) (transformM (g bad) x)
            where
                g bad (CoreVar x) = case lookup x bad of
                                    Nothing -> return $ CoreVar x
                                    Just y -> duplicateExpr y
                g bad x = return x

        f x = return x


inline :: CoreFuncName -> SS CoreExpr
inline name = do
    c <- liftM core get
    let CoreFunc _ args body = c Map.! name
    duplicateExpr $ coreLam args body


template :: CoreFuncName -> [CoreExpr] -> SS CoreExpr
template x xs = do
    s <- get
    let o = CoreApp (CoreFun x) xs
        t = templateNorm $ templateCheck (sBoxed s) o
    if isCorePrim (core s Map.! x) || t == templateNone then return o else do
        let holes = templateHoles o t
        case BiMap.lookupRev t (special s) of
            -- OPTION 2: Previously done
            Just name -> do
                return $ CoreApp (CoreFun name) holes
            -- OPTION 3: New todo
            _ -> do
                let name = uniqueJoin (templateName t) (funcId s)
                fun <- templateGenerate (core s Map.!) name t
                modify $ \s -> s{funcId = funcId s + 1
                                ,special = BiMap.insert name t (special s)
                                ,core = Map.insert name fun (core s)
                                ,templated = True
                                }
                return $ CoreApp (CoreFun name) holes
