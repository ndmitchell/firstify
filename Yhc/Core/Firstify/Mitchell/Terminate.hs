
module Yhc.Core.Firstify.Mitchell.Terminate where

import Yhc.Core
import qualified Data.Homeomorphic as H
import qualified Data.Set as Set


data Terminate = Terminate
    {specs :: H.Homeomorphic CoreExpr1 CoreExpr
    ,specsDone :: [(H.Shell CoreExpr1,CoreExpr)]
    ,inlined :: Set.Set CoreFuncName
    }


mergeTerminate :: Terminate -> Terminate -> Terminate
mergeTerminate t1 t2 = foldl (flip $ uncurry addSpec)
    t1{inlined = inlined t1 `Set.union` inlined t2} (specsDone t2)


addSpec :: H.Shell CoreExpr1 -> CoreExpr -> Terminate -> Terminate
addSpec shell value t = t{specsDone = (shell,value) : specsDone t
                          ,specs = H.insert shell value (specs t)}


allowSpec :: H.Shell CoreExpr1 -> Terminate -> Bool
allowSpec x t = length (H.find x (specs t)) <= 1


addInline :: CoreFuncName -> Terminate -> Terminate
addInline x t = t{inlined = Set.insert x (inlined t)} 


allowInline :: CoreFuncName -> Terminate -> Bool
allowInline x t = not $ x `Set.member` inlined t

