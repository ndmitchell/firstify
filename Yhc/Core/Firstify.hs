
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


---------------------------------------------------------------------
-- REYNOLDS METHOD

reynolds :: Core -> Core
reynolds c = c3
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
        
        ap_ fun args = CoreApp (CoreCon $ name ++ "_" ++ fun) args
            where
                name = if n == 0 then apTyp else apTyp <#> n
                n = length args

        -- then figure out which functions we required


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


data S = S {inlined :: Set.Set CoreFuncName
           ,specialised :: H.Homeomorphic CoreExpr1 ()
           ,special :: [(CoreExpr, CoreFuncName)]
           ,varId :: Int
           ,funcId :: Int
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
step :: Core -> State S Core
step c = return c


{-

-- BEFORE: even = (.) not odd
-- AFTER:  even x = (.) not odd x 
promote :: Core -> State S Core
promote c = do
    let a = arities c



unsaturated :: Core -> CoreExpr -> Bool
unsaturated = False


-}
