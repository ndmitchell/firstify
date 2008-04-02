
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
           ,usedS :: [CoreFuncName]
           
           -- used to loop round
           ,info :: Info
           ,core :: CoreFuncMap
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
    ,iTemplate :: [Template]
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
        s0 = S (emptyTerminate True) BiMap.empty c2 0 (uniqueFuncsNext c2) emptyFunS [] undefined undefined
        c2 = ensureInvariants [NoRecursiveLet,NoCorePos] c


run :: CoreFuncMap -> SS CoreFuncMap
run precore = do
    let cr = Map.map (applyBodyFunc wrapCoreFun) precore
    modify $ \s -> s{info = Info Set.empty (Map.map coreFuncArity cr) Map.empty []
                    ,core = cr}
    step False (order cr)


-- return True if they agree
checkStat :: Info -> FunS -> Bool
checkStat i s = all (`Set.notMember` (iBox i)) (sBox s) &&
                all (\(n,a) -> a == (iArity i Map.! n)) (sArity s) &&
                null (sTemplate s)


step :: Bool -> [CoreFuncName] -> SS CoreFuncMap
step chng (t:odo) = do
    i <- liftM info get
    core <- liftM core get
    let res = maybe True (not . checkStat i) $ Map.lookup t (iFunS i)
    if not res then do
        modify $ \s -> let is = info s in s{info = is{iTemplate = sTemplate (iFunS is Map.! t) ++ iTemplate is}}
        step chng odo
     else do
        modify $ \s -> s{funS = emptyFunS, usedS = []}
        fun <- func (arity i) (boxed i) (inline core) (template core (boxed i)) (core Map.! t)
        let a = coreFuncArity fun
        b <- isBox (boxed i) (coreFuncBody fun)
        let c = a /= iArity i Map.! t ||
                b /= t `Set.member` iBox i
        modify $ \s -> s{info = 
            Info {iBox = (if b then Set.insert t else id) (iBox i)
                 ,iArity = Map.insert t a (iArity i)
                 ,iFunS = Map.insert t (funS s) (iFunS i)
                 ,iTemplate = sTemplate (funS s) ++ iTemplate i}
            ,core = Map.insert t fun core}
        s <- get
        step (chng || c) (usedS s ++ odo)
    where
        arity i name = do
            let res = iArity i Map.! name
            modifyS $ \s -> s{sArity = (name,res) : sArity s}
            return res

        boxed i name = do
            let res = name `Set.member` iBox i
            when (not res) $ modifyS $ \s -> s{sBox = name : sBox s}
            return res

        modifyS f = modify $ \s -> s{funS = f (funS s)}

step True [] = do
    modify $ \s -> s{info = (info s){iTemplate=[]}}
    s <- get
    trace "Simplifying" $ step False (order $ core s)

-- generate the templates and retry
step False [] = do
    i <- liftM info get
    so <- get
    if null $ iTemplate i then do
        liftM core get
     else trace "Templating" $ do
        res <- mapM f $ iTemplate i
        modify $ \s -> s{info = (info s){iTemplate=[]}}
        s <- get
        step False (res ++ order (core so))
    where
        f t = do
            s <- get
            let name = uniqueJoin (templateName t) (funcId s)
            fun <- templateGenerate (core s Map.!) name t
            modify $ \s -> s{funcId = funcId s + 1
                            ,special = BiMap.insert name t (special s)
                            ,core = Map.insert name fun (core s)
                            ,info = (info s){iArity = Map.insert name (coreFuncArity fun) $ iArity (info s)}
                            }
            return name



-- which order should we do this in
-- should be main last, all its dependencies before
-- but skip anything unreachable
order :: CoreFuncMap -> [CoreFuncName]
order core = {- if sort res == sort expect then -} res {- else error "order failed" -}
    where
        res = reverse $ f ["main"] Set.empty
        expect = [name | CoreFunc name _ _ <- Map.elems $ coreReachableMap ["main"] core]
    
        f (t:odo) done
                | isCoreFunc fun && not (t `Set.member` done)
                = t : f (calls++odo) (Set.insert t done)
            where
                calls = [x | CoreFun x <- universe $ coreFuncBody fun]
                fun = core Map.! t

        f (t:odo) done = f odo done
        f [] done = []


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
            b <- boxed x
            if not b then return o else do
                x2 <- inline x
                case x2 of
                    Nothing -> return o
                    Just y -> do
                        on <- f $ CoreApp y xs
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
                (bad,good) <- partitionM (\(a,b) -> return (isCoreLam b) `orM` isBox boxed b) bind
                if null bad
                    then return $ CoreLet bind x
                    else transformM f =<< liftM (coreLet good) (transformM (g bad) x)
            where
                g bad (CoreVar x) = case lookup x bad of
                                    Nothing -> return $ CoreVar x
                                    Just y -> duplicateExpr y
                g bad x = return x

        f x = return x


inline :: CoreFuncMap -> CoreFuncName -> SS (Maybe CoreExpr)
inline core name = do
    let CoreFunc _ args body = core Map.! name
    liftM Just $ duplicateExpr $ coreLam args body


template :: CoreFuncMap -> (CoreFuncName -> SS Bool) -> CoreFuncName -> [CoreExpr] -> SS CoreExpr
template core boxed x xs = do
    t <- liftM templateNorm $ templateCheck2 boxed x xs
    if prim || t == templateNone then return o else do
        s <- get
        let holes = templateHoles o t
        case BiMap.lookupRev t (special s) of
            -- OPTION 2: Previously done
            Just name -> do
                modify $ \s -> s{usedS = name : usedS s}
                return $ CoreApp (CoreFun name) holes
            -- OPTION 3: New todo
            done -> do
                modify $ \s -> s{funS = (funS s){sTemplate = t : sTemplate (funS s)}}
                return $ CoreApp (CoreFun x) xs
        where
            o = CoreApp (CoreFun x) xs
            prim = isCorePrim $ core Map.! x


templateCheck2 :: (CoreFuncName -> SS Bool) -> CoreFuncName -> [CoreExpr] -> SS Template
templateCheck2 isHO x xs = join (CoreApp (CoreFun x)) (map f xs)
    where
        free = collectFreeVars (CoreApp (CoreFun x) xs)
        f (CoreLam vs x) = liftM (CoreLam vs) (f x)
        f (CoreVar x) | x `notElem` free = return $ CoreVar x
        f (CoreApp (CoreFun x) xs) = do
            b <- isHO x
            if b
                then liftM (CoreApp (CoreFun x)) (mapM f xs)
                else join (CoreApp (CoreFun x)) (map f xs)
        f (CoreApp x xs) | isCoreCon x || isCoreFun x = join (CoreApp x) (map f xs)
        f x = join generate (map f children)
            where (children,generate) = uniplate x

        join g xs = do
            xs <- sequence xs
            if any (/= templateNone) xs
                then return $ g xs
                else return templateNone

