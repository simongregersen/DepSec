module DepSec.Lattice

import public DepSec.Poset

%access public export
%hide Prelude.Monad.join
%default total

||| Verified join semilattice
interface JoinSemilattice a where
  join : a -> a -> a
  associative : (x, y, z : a) -> x `join` (y `join` z) = (x `join` y) `join` z
  commutative : (x, y : a)    -> x `join` y = y `join` x
  idempotent  : (x : a)       -> x `join` x = x

||| A well defined join induces a partial ordering.
implementation JoinSemilattice a => Poset a where
  leq x y = (x `join` y = y)
  reflexive = idempotent
  antisymmetric x y lexy leyx =
    rewrite sym $ lexy in
    rewrite commutative x y in
    rewrite sym $ leyx in Refl
  transitive x y z lexy leyx =
    rewrite sym $ leyx in
    rewrite associative x y z in
    rewrite sym $ lexy in Refl

||| A join-semilattice with an identity element (the lattices' bottom)
||| of the join operation.
interface JoinSemilattice a => BoundedJoinSemilattice a where
  Bottom : a
  unitary : (e : a) -> e `join` Bottom = e

||| Decidable partial ordering
decLeq : JoinSemilattice a => DecEq a => (x, y : a) -> Dec (x `leq` y)
decLeq x y = decEq (x `join` y) y

--------------------------------------------------------------------------------
--- Lemmas
--------------------------------------------------------------------------------
leq_bot_x : BoundedJoinSemilattice lt
         => (x : lt)
         -> Bottom `leq` x
leq_bot_x x =
  rewrite commutative Bottom x in
  unitary x

join_x_xy : JoinSemilattice lt
          => (x, y: lt)
          -> join x (join x y) = join x y
join_x_xy x y =
  rewrite associative x x y in
  rewrite idempotent x in Refl

join_y_xy : JoinSemilattice lt
         => (x, y : lt)
         -> join y (join x y) = join x y
join_y_xy x y =
  rewrite commutative x y in
  rewrite associative y y x in
  rewrite idempotent y in Refl
