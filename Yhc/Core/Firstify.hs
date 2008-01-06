
module Yhc.Core.Firstify(reynolds, firstify) where

import Yhc.Core hiding (uniqueBoundVarsCore)
import Yhc.Core.FreeVar3
import Yhc.Core.UniqueId

import Control.Monad.State
import qualified Data.Homeomorphic as H
import qualified Data.Set as Set


---------------------------------------------------------------------
-- REYNOLDS METHOD

reynolds :: Core -> Core
reynolds = error "Yhc.Core.Firstify.reynolds: todo"



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
