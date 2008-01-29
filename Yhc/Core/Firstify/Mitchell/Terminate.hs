
module Yhc.Core.Firstify.Mitchell.Terminate where

import Yhc.Core
import qualified Data.Homeomorphic as H

data Terminate = Terminate
    {specs :: H.Homeomorphic CoreExpr1 CoreExpr
    ,specsDone :: [(CoreExpr1,CoreExpr)]
    ,inlined :: Set.Set CoreFuncName
    }


mergeTerminate :: Terminate -> Terminate -> Terminate
mergeTerminate t1 t2 = foldl (uncurry addSpecs)
    t1{inlined = inlined t1 `Set.union` inlined t2} (specsDone t2)


addSpecs :: CoreExpr1 -> CoreExpr -> Terminate -> Terminate
addSpecs shell value t = t{specsDone = (shell,value) : specsDone t
                          ,specs = H.insert shell value (specs t)}

addInline :: CoreFuncName -> Terminate -> Terminate
addInline x t = t{inlined = Set.insert x (inlined t)} 
