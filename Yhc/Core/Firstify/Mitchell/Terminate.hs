
module Yhc.Core.Firstify.Mitchell.Terminate(
    Terminate, emptyTerminate,
    addInline, askInline,
    addSpec, askSpec, cloneSpec
    ) where

import qualified Data.Homeomorphic as H
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace
import Yhc.Core
import Yhc.Core.Util


data Terminate = Terminate
    {verbose :: Bool
    ,terminate :: Map.Map CoreFuncName Term
    }

data Term = Term
    {specs :: [H.Homeomorphic CoreExpr1 CoreExpr]
    ,inlined :: Set.Set CoreFuncName
    }


homeoOrder = 8 :: Int

insertH key val [] = error "Logic fault, insertH"
insertH key val (x:xs) | isNothing (H.findOne key x) = H.insert key val x : xs
                       | otherwise = x : insertH key val xs

findH key xs = if any null res then [] else concat res
    where res = map (H.find key) xs



get name t = Map.findWithDefault emptyTerm name (terminate t)
modify t name op = t{terminate = Map.insert name (op $ get name t) (terminate t)}

logger t msg answer = (if verbose t && not answer then trace msg else id) answer


emptyTerminate :: Bool -> Terminate
emptyTerminate b = Terminate b Map.empty


emptyTerm :: Term
emptyTerm = Term (replicate homeoOrder H.empty) Set.empty


addInline :: CoreFuncName -> CoreFuncName -> Terminate -> Terminate
addInline within on t = modify t within $ \x -> x{inlined = Set.insert on $ inlined x}


askInline :: CoreFuncName -> CoreFuncName -> Terminate -> Bool
askInline within on t = logger t ("Skipped inlining of: " ++ on ++ " within " ++ within) $
    on `Set.notMember` inlined (get within t)


addSpec :: CoreFuncName -> CoreExpr -> Terminate -> Terminate
addSpec within on t = modify t within $ \x -> x{specs = insertH (specKey on) on $ specs x}

specKey = shellify . blurVar


askSpec :: CoreFuncName -> CoreExpr -> Terminate -> Bool
askSpec within on t = logger t ("Skipped spec of:\n" ++ show on ++ "\nbecause of\n" ++ show res) $
    length res < 1
    where
        res = findH (specKey on) $ specs $ get within t


cloneSpec :: CoreFuncName -> CoreFuncName -> Terminate -> Terminate
cloneSpec from to t = case Map.lookup from (terminate t) of
                           Nothing -> t
                           Just y -> t{terminate = Map.insert to y{inlined=Set.empty} $ terminate t}
