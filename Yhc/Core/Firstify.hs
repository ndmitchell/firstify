
module Yhc.Core.Firstify(reynolds, firstify) where

import Yhc.Core hiding (uniqueBoundVarsCore)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Homeomorphic as H
import qualified Data.Set as Set
import qualified Data.Map as Map


g `on` f = \x y -> f x `g` f y

---------------------------------------------------------------------
-- REYNOLDS METHOD

reynolds :: Core -> Core
reynolds c = c3{coreDatas = newDatas ++ coreDatas c3
               ,coreFuncs = newFuncs ++ coreFuncs c3}
    where
        -- set up some information
        c2 = transformExpr appRules c
        arr = Map.fromList [(coreFuncName x, coreFuncArity x) | x <- coreFuncs c]
        apFun = findApFun c
        apTyp = findApTyp c
        
        a <#> b | isDigit (last a) = a ++ "_" ++ show b
                | otherwise = a ++ show b

        appRules (CoreFun x) = CoreApp (CoreFun x) []
        appRules (CoreApp x []) | not $ isCoreFun x = x
        appRules (CoreApp (CoreApp x y) z) = CoreApp x (y++z)
        appRules x = x

        -- just transform the thing
        c3 = transformExpr defunc c2

        defunc (CoreApp (CoreFun x) xs) =
            case compare (length xs) a of
                EQ -> CoreApp (CoreFun x) xs
                LT -> ap_ x xs
                GT -> ap (CoreApp (CoreFun x) yes) no
                    where (yes,no) = splitAt a xs
            where a = arr Map.! x
        defunc (CoreApp x xs) | not $ isCoreCon x = ap x xs
        defunc x = x

        ap  fun args = CoreApp (CoreFun name) (fun:args)
            where
                name = if n == 1 then apFun else apFun <#> n
                n = length args
        
        ap_ fun args = CoreApp (CoreCon $ apTypGen fun (length args)) args

        apTypGen fun n = (if n == 0 then apTyp else apTyp <#> n) ++ "_" ++ fun

        -- then figure out which functions we required
        splitApFun x = if null s then 1 else read s
            where s = dropWhile (== '_') $ drop (length apFun) x
        
        aps = [splitApFun x | CoreFun x <- universeExpr c3, apFun `isPrefixOf` x]

        arityApps = [CoreFunc (apFun <#> i) ("x":vars) $
                              foldl (\x y -> CoreApp (CoreFun apFun) [x,CoreVar y]) (CoreVar "x") vars
                    | i <- Set.toAscList $ Set.fromList aps, i /= 1
                    , let vars = ['y':show j | j <- [1..i]] ]

        splitApTyp x = if not $ isDigit $ head s then (0, s)
                       else let (a,_:b) = break (== '_') s in (read a, b)
            where s = dropWhile (== '_') $ drop (length apTyp) x

        dats = map head $ groupBy ((==) `on` snd) $ sort
               [splitApTyp x | CoreCon x <- universeExpr c3, apTyp `isPrefixOf` x]

        newDatas = [CoreData apTyp [] $
                        [CoreCtor (apTypGen c j) [('T':show k, Nothing) | k <- [1..j]]
                        | (i,c) <- dats, j <- [i..(arr Map.! c) - 1]]
                   ]

        mainAp = CoreFunc apFun ["x","z"] $ CoreCase (CoreVar "x") $
                 [(PatCon (apTypGen c j) vars,
                  CoreApp (if j+1 == n then CoreFun c else CoreCon $ apTypGen c (j+1))
                          (map CoreVar vars ++ [CoreVar "z"])
                  )
                 | (i,c) <- dats, let n = arr Map.! c, j <- [i..n-1]
                 , let vars = ['y':show k | k <- [1..j]] ]

        newFuncs = mainAp : arityApps


findApFun :: Core -> CoreFuncName
findApFun c = findName (map coreFuncName $ coreFuncs c) "ap"

findApTyp :: Core -> String
findApTyp c = findName (concatMap f $ coreDatas c) "Ap"
    where f x = coreDataName x : map coreCtorName (coreDataCtors x)

-- find a name pre# (where # is blank or a number)
-- such that pre# is not a prefix of any of the seen set
findName :: [String] -> String -> String
findName seen pre = if null seen2 then pre else pre ++ show (head $ filter isValid [1..])
    where
        isValid i = not $ any ((pre ++ show i) `isPrefixOf`) seen2
        seen2 = filter (pre `isPrefixOf`) seen


---------------------------------------------------------------------
-- MY METHOD - FROM MY THESIS

type SS a = State S a

data S = S {inlined :: Set.Set CoreFuncName  -- which have been inlined (termination check)
           ,specialised :: H.Homeomorphic CoreExpr1 () -- which have been specialised (termination check)
           ,special :: [(CoreExpr, CoreFuncName)] -- which special variants do we have (CoreVar "" is wildcard)
           ,varId :: Int -- what is the next variable id to use
           ,funcId :: Int -- what is the next function id to use
           }


instance UniqueId S where
    getId = varId
    putId x s = s{varId = x}


-- First lambda lift (only top-level functions).
-- Then perform the step until you have first-order.
firstify :: Core -> Core
firstify c = evalState (fixM step =<< uniqueBoundVarsCore c2) s0
    where
        s0 = S Set.empty H.empty [] 0 (uniqueFuncsNext c2)
        c2 = ensureInvariants [NoRecursiveLet,NoCoreLam] c


fixM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixM f x = do
    x2 <- f x
    if x == x2 then return x2 else fixM f x2 


-- In each step first inline all top-level function bindings
-- and let's that appear to be bound to an unsaturated
--
-- Then specialise each value
step :: Core -> SS Core
step = fixM (promote * inline * specialise)
    where
        (*) a b x = do
            x2 <- a x
            if x == x2 then b x2 else return x2


-- BEFORE: even = (.) not odd
-- AFTER:  even x = (.) not odd x 
promote :: Core -> SS Core
promote c = return c


-- BEFORE: box = [even]
-- AFTER:  all uses of box are inlined
inline :: Core -> SS Core
inline c = return c


-- BEFORE: map even x
-- AFTER:  map_even x
specialise :: Core -> SS Core
specialise c = return c



