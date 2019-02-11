module Examples.Declassification.TimeHatch

import System

import DepSec.DIO
import DepSec.Labeled
import DepSec.Declassification

import Examples.TwoPointLattice

%default total

--------------------------------------------------------------------------------
-- Library
--------------------------------------------------------------------------------
data Time : Type where
  ||| TCB
  MkTime : (t : Integer) -> Time

implementation Eq Time where
  (MkTime t1) == (MkTime t2) = t1 == t2

implementation Ord Time where
  compare (MkTime t1) (MkTime t2) = compare t1 t2

tick : DIO l Time
tick = pure (MkTime !(lift time))

print : String -> DIO L ()
print x = lift $ putStrLn x

usleep : (i : Int) -- microseconds
      -> {auto prf : So (i >= fromInteger 0)}
      -> DIO L ()
usleep i = lift $ usleep i

TimeHatch : Time -> Type
TimeHatch t = (t' : Time ** t <= t' = True) -> Labeled H Nat -> Labeled L Nat

data Fuel = Dry | More (Lazy Fuel)

--------------------------------------------------------------------------------
-- Bob (untrusted)
--------------------------------------------------------------------------------
bob : Fuel
   -> (secret : Labeled H Nat)
   -> TimeHatch t
   -> DIO L ()
bob Dry _ _ = pure ()
bob (More x) secret timeHatch {t} =
  do time <- tick
     case decEq (t <= time) True of
       Yes prf =>
         let declassified : Labeled L Nat  = timeHatch (time ** prf) secret
         in print $ "Yay! The secret is: " ++ cast !(unlabel declassified)
       No _ =>
          do print "No secret for me yet. Trying again in 500 ms ..."
             usleep 500000
             bob x secret timeHatch
     pure ()

--------------------------------------------------------------------------------
-- Alice (trusted)
--------------------------------------------------------------------------------
partial
forever : Fuel
forever = More forever

partial
alice : DIO L ()
alice =
  do let secret : Labeled H Nat = label 42
     (MkTime t) <- tick
     let declassifyTime = MkTime (t + 4)
     let hatch : TimeHatch declassifyTime = tokenHatch (\t' => declassifyTime <= t' = True)
     bob forever secret hatch

partial
main : IO ()
main = run alice
