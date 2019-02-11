module Examples.TwoPointLattice

import public DepSec.Lattice

%access public export

data TwoPoint = H | L

implementation JoinSemilattice TwoPoint where
  join L L = L
  join L H = H
  join H L = H
  join H H = H

  associative L L L = Refl
  associative L L H = Refl
  associative L H L = Refl
  associative L H H = Refl
  associative H L L = Refl
  associative H H L = Refl
  associative H L H = Refl
  associative H H H = Refl

  commutative L L = Refl
  commutative L H = Refl
  commutative H L = Refl
  commutative H H = Refl

  idempotent L = Refl
  idempotent H = Refl

implementation BoundedJoinSemilattice TwoPoint where
  Bottom = L
  unitary H = Refl
  unitary L = Refl
