
module Yhc.Core.Firstify.Mitchell.Terminate(
    Terminate, emptyTerminate,
    addInline, askInline,
    addSpec, askSpec, cloneSpec
    ) where

import qualified Data.Homeomorphic as H
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace
import Yhc.Core
import Yhc.Core.Firstify.Mitchell.Util


data Terminate = Terminate
    {verbose :: Bool
    ,terminate :: Map.Map CoreFuncName Term
    }

data Term = Term
    {specs :: H.Homeomorphic CoreExpr1 CoreExpr
    ,inlined :: Set.Set CoreFuncName
    }


get name t = Map.findWithDefault emptyTerm name (terminate t)
modify t name op = t{terminate = Map.insert name (op $ get name t) (terminate t)}

logger t msg answer = (if verbose t && not answer then trace msg else id) answer


emptyTerminate :: Bool -> Terminate
emptyTerminate b = Terminate b Map.empty


emptyTerm :: Term
emptyTerm = Term H.empty Set.empty


addInline :: Terminate -> CoreFuncName -> CoreFuncName -> Terminate
addInline t within on = modify t within $ \x -> x{inlined = Set.insert on $ inlined x}


askInline :: Terminate -> CoreFuncName -> CoreFuncName -> Bool
askInline t within on = logger t ("Skipped inlining of: " ++ on ++ " within " ++ within) $
    on `Set.notMember` inlined (get within t)


addSpec :: Terminate -> CoreFuncName -> CoreExpr -> Terminate
addSpec t within on = modify t within $ \x -> x{specs = H.insert (specKey on) on $ specs x}

specKey = shellify . blurVar


askSpec :: Terminate -> CoreFuncName -> CoreExpr -> Bool
askSpec t within on = logger t ("Skipped spec of:\n" ++ show on ++ "\nbecause of\n" ++ show res) $
    length res <= 1
    where
        res = H.find (specKey on) $ specs $ get within t


cloneSpec :: CoreFuncName -> CoreFuncName -> Terminate -> Terminate
cloneSpec from to t = case Map.lookup from (terminate t) of
                           Nothing -> t
                           Just y -> t{terminate = Map.insert to y{inlined=Set.empty} $ terminate t}
