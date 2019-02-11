module Examples.Declassificcation.PWHatch

import Control.ST
import Data.Vect

import DepSec.DIO
import DepSec.Labeled
import DepSec.Ref

import Examples.TwoPointLattice

%default total

printBool : Bool -> DIO L ()
printBool False = lift $ putStrLn "Wrong guess"
printBool True = lift $ putStrLn "Correct guess!"

--------------------------------------------------------------------------------
-- Library code
--------------------------------------------------------------------------------
DIO' : l -> (ty : Type) -> List (Action ty) -> Type
DIO' l = ST (DIO l)

data Counter : Nat -> Type where
  ||| TCB
  MkCounter : (n : Nat) -> Counter n

Attempts : Nat -> Type
Attempts = State . Counter

decCounter : Counter (S n) -> Counter n
decCounter _ {n} = MkCounter n

limit : (f : a -> b)
     -> (arg : a)
     -> DIO' l b [attempts ::: Attempts (S n) :-> Attempts n]
limit f arg {attempts} = returning (f arg) $ update attempts decCounter

hatch : (labeled : Labeled H Int) ->
        (guess : Int) ->
        DIO' l Bool [attempts ::: Attempts (S n) :-> Attempts n]
hatch (MkLabeled v) = limit (\g => g == v)

||| TCB
run : DIO' l a [] -> IO a
run = DepSec.DIO.run . Control.ST.run

--------------------------------------------------------------------------------
-- Bob (untrusted)
--------------------------------------------------------------------------------
bob : Labeled H Int ->
      DIO' L () [attempts ::: Attempts (3 + n) :-> Attempts n]
bob secret =
  do x1 <- hatch secret 1
     lift $ printBool x1
     x2 <- hatch secret 2
     lift $ printBool x2
     x3 <- hatch secret 42
     lift $ printBool x3
     -- x4 <- hatch secret 4 -- illegal!
     pure ()

--------------------------------------------------------------------------------
-- Alice (trusted)
--------------------------------------------------------------------------------
alice : DIO' L () []
alice =
  do attempts <- new (MkCounter 3)
     let secret : Labeled H Int = label 42
     bob secret
     delete attempts

main : IO ()
main = run $ alice
