module Examples.AuthorityLattice

import public DepSec.Lattice

%access public export
%default total

data Principal : Type where
  Top : Principal
  Alice : Principal
  Bob : Principal
  Chuck : Principal
  Bot : Principal

implementation JoinSemilattice Principal where
  join Top b = Top
  join Alice Top =Top
  join Alice Alice = Alice
  join Alice Bob = Top
  join Alice Chuck = Top
  join Alice Bot = Alice
  join Bob Top = Top
  join Bob Alice = Top
  join Bob Bob = Bob
  join Bob Chuck = Top
  join Bob Bot = Bob
  join Chuck Top = Top
  join Chuck Alice = Top
  join Chuck Bob = Top
  join Chuck Chuck = Chuck
  join Chuck Bot = Chuck
  join Bot b = b

  associative Top b c = Refl
  associative Alice Top c = Refl
  associative Alice Alice Top = Refl
  associative Alice Alice Alice = Refl
  associative Alice Alice Bob = Refl
  associative Alice Alice Chuck = Refl
  associative Alice Alice Bot = Refl
  associative Alice Bob Top = Refl
  associative Alice Bob Alice = Refl
  associative Alice Bob Bob = Refl
  associative Alice Bob Chuck = Refl
  associative Alice Bob Bot = Refl
  associative Alice Chuck Top = Refl
  associative Alice Chuck Alice = Refl
  associative Alice Chuck Bob = Refl
  associative Alice Chuck Chuck = Refl
  associative Alice Chuck Bot = Refl
  associative Alice Bot c = Refl
  associative Bob Top c = Refl
  associative Bob Alice Top = Refl
  associative Bob Alice Alice = Refl
  associative Bob Alice Bob = Refl
  associative Bob Alice Chuck = Refl
  associative Bob Alice Bot = Refl
  associative Bob Bob Top = Refl
  associative Bob Bob Alice = Refl
  associative Bob Bob Bob = Refl
  associative Bob Bob Chuck = Refl
  associative Bob Bob Bot = Refl
  associative Bob Chuck Top = Refl
  associative Bob Chuck Alice = Refl
  associative Bob Chuck Bob = Refl
  associative Bob Chuck Chuck = Refl
  associative Bob Chuck Bot = Refl
  associative Bob Bot c = Refl
  associative Chuck Top c = Refl
  associative Chuck Alice Top = Refl
  associative Chuck Alice Alice = Refl
  associative Chuck Alice Bob = Refl
  associative Chuck Alice Chuck = Refl
  associative Chuck Alice Bot = Refl
  associative Chuck Bob Top = Refl
  associative Chuck Bob Alice = Refl
  associative Chuck Bob Bob = Refl
  associative Chuck Bob Chuck = Refl
  associative Chuck Bob Bot = Refl
  associative Chuck Chuck Top = Refl
  associative Chuck Chuck Alice = Refl
  associative Chuck Chuck Bob = Refl
  associative Chuck Chuck Chuck = Refl
  associative Chuck Chuck Bot = Refl
  associative Chuck Bot c = Refl
  associative Bot b c = Refl

  commutative Top Top = Refl
  commutative Top Alice = Refl
  commutative Top Bob = Refl
  commutative Top Chuck = Refl
  commutative Top Bot = Refl
  commutative Alice Top = Refl
  commutative Alice Alice = Refl
  commutative Alice Bob = Refl
  commutative Alice Chuck = Refl
  commutative Alice Bot = Refl
  commutative Bob Top = Refl
  commutative Bob Alice = Refl
  commutative Bob Bob = Refl
  commutative Bob Chuck = Refl
  commutative Bob Bot = Refl
  commutative Chuck Top = Refl
  commutative Chuck Alice = Refl
  commutative Chuck Bob = Refl
  commutative Chuck Chuck = Refl
  commutative Chuck Bot = Refl
  commutative Bot Top = Refl
  commutative Bot Alice = Refl
  commutative Bot Bob = Refl
  commutative Bot Chuck = Refl
  commutative Bot Bot = Refl

  idempotent Top = Refl
  idempotent Alice = Refl
  idempotent Bob = Refl
  idempotent Chuck = Refl
  idempotent Bot = Refl
