
module Yhc.Core.Firstify(reynolds, firstify) where

import Yhc.Core.Firstify.Reynolds

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



