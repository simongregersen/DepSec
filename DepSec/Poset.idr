module DepSec.Poset

%access public export
%default total
%hide Prelude.Monad.join

||| Verified partial ordering
interface Poset a where
  leq           : a -> a -> Type
  reflexive     : (x : a) -> x `leq` x
  antisymmetric : (x, y : a) -> x `leq` y -> y `leq` x -> x = y
  transitive    : (x, y, z : a) -> x `leq` y -> y `leq` z -> x `leq` z
