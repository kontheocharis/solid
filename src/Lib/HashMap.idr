module Lib.HashMap

import Data.HashMap.Internal
import Data.Hashable
import Decidable.Equality
import Utils

-- Dependent version of HashMap, see
-- https://github.com/Z-snails/idris2-hashmap/blob/main/src/Data/HashMap.idr

export
data HashDMap : (key : Type) -> (val : key -> Type) -> Type where
    Empty : Hashable key => Eq key => HashDMap key val
    Trie : HAMT key val -> Hashable key => Eq key => HashDMap key val
    
%name HashDMap hm

export
empty : Hashable key => Eq key => HashDMap key val
empty = Empty

export
lookup : SemiDecEq key => (k : key) -> HashDMap key val -> Maybe (val k)
lookup key Empty = Nothing
lookup key (Trie hamt) = case (lookup (==) key hamt) of
  Just x => case semiDecEq (fst x) key of
    Just Refl => Just (snd x)
    _ => Nothing -- should never happen
  Nothing => Nothing

export
insert : (k : key) -> val k -> HashDMap key val -> HashDMap key val
insert key val Empty = Trie $ singleton key val
insert key val (Trie hamt) = Trie $ insert (==) key val hamt

export
delete : key -> HashDMap key val -> HashDMap key val
delete key Empty = Empty
delete key (Trie hamt) = case delete (==) key hamt of
    Just hamt' => Trie hamt'
    Nothing => Empty

export
foldWithKey : (f : (k : key) -> val k -> acc -> acc) -> acc -> HashDMap key val -> acc
foldWithKey f z Empty = z
foldWithKey f z (Trie hamt) = foldWithKey f z hamt

export
toList : HashDMap key val -> List (k ** val k)
toList hm = foldWithKey (\key, val, acc => (key ** val) :: acc) [] hm

export
keys : HashDMap k v -> List k
keys hm = foldWithKey (\key, val, acc => key :: acc) [] hm

export
fromList : Hashable key => Eq key => List (k ** val k) -> HashDMap key val
fromList lst = foldr (\(k ** v) => insert k v) empty lst

export
Show key => (forall k . Show (val k)) => Show (HashDMap key val) where
    show hm = "fromList \{show $ toList hm}"