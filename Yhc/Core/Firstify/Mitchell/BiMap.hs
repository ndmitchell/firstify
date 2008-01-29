
module Yhc.Core.Firstify.Mitchell.BiMap(
    BiMap, empty, lookup, lookupRev, insert
    ) where


import Prelude hiding (lookup)
import qualified Data.Map as Map

data BiMap key val = BiMap (Map.Map key val) (Map.Map val key)

empty :: BiMap k v
empty = BiMap Map.empty Map.empty

lookup :: Ord k => k -> BiMap k v -> Maybe v
lookup k (BiMap a b) = Map.lookup k a

lookupRev :: Ord v => v -> BiMap k v -> Maybe k
lookupRev v (BiMap a b) = Map.lookup v b

insert :: (Ord k, Ord v) => k -> v -> BiMap k v -> BiMap k v
insert k v (BiMap a b) = BiMap (Map.insert k v a) (Map.insert v k b)
