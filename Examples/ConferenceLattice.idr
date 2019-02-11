module Examples.ConferenceLattice

import public DepSec.Lattice
import Decidable.Equality
import Pruviloj.Derive.DecEq
import Pruviloj.Disjoint
import Pruviloj.Injective

%language ElabReflection
%access public export

data Id : Type where
  Top : Id
  Nat : Nat -> Id
  Bot : Id

Uid : Type
Uid = Id

Sid : Type
Sid = Id

natInjective : (Nat a) = (Nat b) -> a = b
natInjective Refl = Refl

DecEq Id where
  decEq Top Top = Yes Refl
  decEq Top (Nat k) = No (%runElab disjoint)
  decEq Top Bot = No (%runElab disjoint)
  decEq (Nat k) Top = No (%runElab disjoint)
  decEq (Nat k) (Nat j) with (decEq k j)
    | (Yes prf) = Yes $ cong prf
    | (No contra) = No $ \a => contra $ natInjective a
  decEq (Nat k) Bot = No (%runElab disjoint)
  decEq Bot Top = No (%runElab disjoint)
  decEq Bot (Nat k) = No (%runElab disjoint)
  decEq Bot Bot = Yes Refl

Eq Id where
  Top == Top         = True
  Top == (Nat k)     = False
  Top == Bot         = False
  (Nat k) == Top     = False
  (Nat k) == (Nat j) = k == j
  (Nat k) == Bot     = False
  Bot == Top         = False
  Bot == (Nat k)     = False
  Bot == Bot         = True

data Compartment : Type where
  U  : Uid -> Compartment
  A  : Uid -> Sid -> Compartment
  PC : Uid -> Sid -> Compartment

total
joinId : (x, y : Id) -> Id
joinId Top y = Top
joinId (Nat k) Top = Top
joinId (Nat k) (Nat j) with (decEq k j)
  | (Yes _) = Nat k
  | (No _) = Top
joinId (Nat k) Bot = (Nat k)
joinId Bot y = y

total
joinComp : (x , y : Compartment) -> Compartment
joinComp (U x) (U y) = U (joinId x y)
joinComp (U x) (A y z) = A (joinId x y) z
joinComp (U x) (PC y z) = PC y z
joinComp (A x z) (U y) = A (joinId x y) z
joinComp (A x z) (A y w) = A (joinId x y) (joinId z w)
joinComp (A x z) (PC y w) = PC y (joinId z w)
joinComp (PC x z) (U y) = PC x z
joinComp (PC x z) (A y w) = PC x (joinId z w)
joinComp (PC x z) (PC y w) = PC (joinId x y) (joinId z w)

lemma1 : a = b -> joinId (Nat a) (Nat b) = (Nat a)
lemma1 {a} {b} prf with (decEq a b)
  | (Yes x) = Refl
  | (No contra) = void $ contra prf

lemma2 : (a = b -> Void) -> joinId (Nat a) (Nat b) = Top
lemma2 {a} {b} contra with (decEq a b)
  | (Yes prf) = void $ contra prf
  | (No f) = Refl

lemma3 : a = b -> (b = c -> Void) -> a = c -> Void
lemma3 prf contra prf' = contra $ trans (sym prf) prf'

implementation JoinSemilattice Id where
  join = joinId
  associative Top y z = Refl
  associative (Nat k) Top z = Refl
  associative (Nat k) (Nat j) Top with (decEq k j)
    | (Yes prf) = Refl
    | (No contra) = Refl
  associative (Nat k) (Nat j) (Nat i) with (decEq k j, decEq j i)
    | (Yes prf, Yes prf') =
        rewrite lemma1 prf in
        rewrite lemma1 prf' in
        rewrite lemma1 (trans prf prf') in
        lemma1 prf
    | (Yes prf, No contra) =
        rewrite lemma1 prf in
        rewrite lemma2 contra in
        rewrite lemma2 $ lemma3 prf contra in
        Refl
    | (No contra, Yes prf) =
        rewrite lemma2 contra in
        rewrite lemma1 prf in
        lemma2 contra
    | (No contra, No contra') =
        rewrite lemma2 contra in
        rewrite lemma2 contra' in
        Refl
  associative (Nat k) (Nat j) Bot with (decEq k j)
    | (Yes _) = Refl
    | (No _) = Refl
  associative (Nat k) Bot z = Refl
  associative Bot y z = Refl

  commutative Top Top = Refl
  commutative Top (Nat k) = Refl
  commutative Top Bot = Refl
  commutative (Nat k) Top = Refl
  commutative (Nat k) (Nat j) with (decEq k j)
    | (Yes prf) = rewrite lemma1 $ sym prf in cong prf
    | (No contra) = sym $ lemma2 $ negEqSym contra
  commutative (Nat k) Bot = Refl
  commutative Bot Top = Refl
  commutative Bot (Nat k) = Refl
  commutative Bot Bot = Refl

  idempotent Top = Refl
  idempotent (Nat k) with (decEq k k)
    | (Yes _) = Refl
    | (No contra) = void $ contra Refl
  idempotent Bot = Refl

implementation BoundedJoinSemilattice Id where
  Bottom = Bot

  unitary Top = Refl
  unitary (Nat k) = Refl
  unitary Bot = Refl

implementation JoinSemilattice Compartment where
  join = joinComp

  associative (U x) (U y) (U z) = cong $ associative x y z
  associative (U x) (U y) (A z w) = rewrite associative x y z in Refl
  associative (U x) (U y) (PC z w) = Refl
  associative (U x) (A y w) (U z) = rewrite associative x y z in Refl
  associative (U x) (A y w) (A z s) = rewrite associative x y z in Refl
  associative (U x) (A y w) (PC z s) = Refl
  associative (U x) (PC y w) (U z) = Refl
  associative (U x) (PC y w) (A z s) = Refl
  associative (U x) (PC y w) (PC z s) = Refl
  associative (A x w) (U y) (U z) = rewrite associative x y z in Refl
  associative (A x w) (U y) (A z s) = rewrite associative x y z in Refl
  associative (A x w) (U y) (PC z s) = Refl
  associative (A x w) (A y s) (U z) = rewrite associative x y z in Refl
  associative (A x w) (A y s) (A z t) =
    rewrite associative x y z in
    rewrite associative w s t in Refl
  associative (A x w) (A y s) (PC z t) = rewrite associative w s t in Refl
  associative (A x w) (PC y s) (U z) = Refl
  associative (A x w) (PC y s) (A z t) = rewrite associative w s t in Refl
  associative (A x w) (PC y s) (PC z t) = rewrite associative w s t in Refl
  associative (PC x w) (U y) (U z) = Refl
  associative (PC x w) (U y) (A z s) = Refl
  associative (PC x w) (U y) (PC z s) = Refl
  associative (PC x w) (A y s) (U z) = Refl
  associative (PC x w) (A y s) (A z t) = rewrite associative w s t in Refl
  associative (PC x w) (A y s) (PC z t) = rewrite associative w s t in Refl
  associative (PC x w) (PC y s) (U z) = Refl
  associative (PC x w) (PC y s) (A z t) = rewrite associative w s t in Refl
  associative (PC x w) (PC y s) (PC z t) =
    rewrite associative x y z in
    rewrite associative w s t in Refl

  commutative (U x) (U y) = cong $ commutative x y
  commutative (U x) (A y z) = rewrite commutative x y in Refl
  commutative (U x) (PC y z) = Refl
  commutative (A x z) (U y) = rewrite commutative x y in Refl
  commutative (A x z) (A y w) =
    rewrite commutative x y in
    rewrite commutative z w in
    Refl
  commutative (A x z) (PC y w) = rewrite commutative w z in Refl
  commutative (PC x z) (U y) = Refl
  commutative (PC x z) (A y w) = rewrite commutative z w in Refl
  commutative (PC x z) (PC y w) =
    rewrite commutative x y in
    rewrite commutative z w in
    Refl

  idempotent (U x) = cong $ idempotent x
  idempotent (A x y) =
     rewrite idempotent x in
     rewrite idempotent y in
     Refl
  idempotent (PC x y) =
     rewrite idempotent x in
     rewrite idempotent y in
     Refl

implementation BoundedJoinSemilattice Compartment where
  Bottom = U Bot

  unitary (U x) = cong $ unitary x
  unitary (A x y) = rewrite unitary x in Refl
  unitary (PC x y) = Refl

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------
U_leq_A : U uid `leq` A uid sid
U_leq_A {uid} = rewrite reflexive uid in Refl

A_leq_PC : A uid1 sid `leq` PC uid2 sid
A_leq_PC {sid} = rewrite reflexive sid in Refl
