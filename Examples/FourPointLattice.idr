module Examples.FourPointLattice

import public DepSec.Lattice

%access public export

data FourPoint = H | M1 | M2 | L

implementation JoinSemilattice FourPoint where
  join H _ = H
  join _ H = H
  join L x = x
  join x L = x
  join M1 M1 = M1
  join M1 M2 = H
  join M2 M1 = H
  join M2 M2 = M2

  associative H x y = Refl
  associative M1 H H = Refl
  associative M1 H M1 = Refl
  associative M1 H M2 = Refl
  associative M1 H L = Refl
  associative M1 M1 H = Refl
  associative M1 M1 M1 = Refl
  associative M1 M1 M2 = Refl
  associative M1 M1 L = Refl
  associative M1 M2 H = Refl
  associative M1 M2 M1 = Refl
  associative M1 M2 M2 = Refl
  associative M1 M2 L = Refl
  associative M1 L H = Refl
  associative M1 L M1 = Refl
  associative M1 L M2 = Refl
  associative M1 L L = Refl
  associative M2 H H = Refl
  associative M2 H M1 = Refl
  associative M2 H M2 = Refl
  associative M2 H L = Refl
  associative M2 M1 H = Refl
  associative M2 M1 M1 = Refl
  associative M2 M1 M2 = Refl
  associative M2 M1 L = Refl
  associative M2 M2 H = Refl
  associative M2 M2 M1 = Refl
  associative M2 M2 M2 = Refl
  associative M2 M2 L = Refl
  associative M2 L H = Refl
  associative M2 L M1 = Refl
  associative M2 L M2 = Refl
  associative M2 L L = Refl
  associative L H H = Refl
  associative L H M1 = Refl
  associative L H M2 = Refl
  associative L H L = Refl
  associative L M1 H = Refl
  associative L M1 M1 = Refl
  associative L M1 M2 = Refl
  associative L M1 L = Refl
  associative L M2 H = Refl
  associative L M2 M1 = Refl
  associative L M2 M2 = Refl
  associative L M2 L = Refl
  associative L L H = Refl
  associative L L M1 = Refl
  associative L L M2 = Refl
  associative L L L = Refl

  commutative H H = Refl
  commutative H M1 = Refl
  commutative H M2 = Refl
  commutative H L = Refl
  commutative M1 H = Refl
  commutative M1 M1 = Refl
  commutative M1 M2 = Refl
  commutative M1 L = Refl
  commutative M2 H = Refl
  commutative M2 M1 = Refl
  commutative M2 M2 = Refl
  commutative M2 L = Refl
  commutative L H = Refl
  commutative L M1 = Refl
  commutative L M2 = Refl
  commutative L L = Refl

  idempotent H = Refl
  idempotent M1 = Refl
  idempotent M2 = Refl
  idempotent L = Refl

implementation BoundedJoinSemilattice FourPoint where
  Bottom = L
  unitary H = Refl
  unitary L = Refl
  unitary M1 = Refl
  unitary M2 = Refl
