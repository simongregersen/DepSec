module Examples.Auction

import Data.Vect
import Data.Vect.Quantifiers

import DepSec.Labeled
import DepSec.DIO
import DepSec.Declassification

import Examples.TwoPointLattice

%default total
%access export

--------------------------------------------------------------------------------
--- Auction Hatch Example
--------------------------------------------------------------------------------
Bid : Type
Bid = (String, Nat)

BidLog : Nat -> Type
BidLog n = Vect n (Labeled H Bid)

data MaxL : Bid -> Labeled H Bid -> Type where
  IsMaxL : (b1 : Bid)
        -> (b2 : Labeled H Bid)
        -> (b : Bid ** (maximum (snd b1) (snd b) = (snd b1), label b = b2))
        -> MaxL b1 b2

data MaxBid : Bid -> BidLog n -> Type where
  IsMax : (bid : Bid)
       -> (bids : BidLog n)
       -> All (\b => MaxL bid b) bids
       -> MaxBid bid bids

HighestBid : BidLog _ -> Bid -> Type
HighestBid = \rec, b => (Elem (label b) rec, MaxBid b rec)

HighestBidHatch : BidLog _ -> Type
HighestBidHatch rec = Labeled H (b : Bid ** HighestBid rec b) -> Labeled L Bid

HatchPair : Nat -> Type
HatchPair n = (rec : BidLog n ** Labeled H (b : Bid ** HighestBid rec b) -> Labeled L Bid)

aHatchPair : HatchPair 2
aHatchPair =
  let rec : BidLog 2 = [(label ("Alice", 1337)), (label ("Bob", 1336))]
  in predicateHatch rec HighestBid

printBid : Labeled L Bid -> DIO L ()
printBid (MkLabeled (n, b)) = lift $ putStrLn n

--------------------------------------------------------------------------------
-- UTCB
--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------
maximum_trans : maximum a c = a -> maximum b a = b -> maximum b c = b
maximum_trans {a} {b} {c} prf prf1 =
  rewrite sym prf1 in
  rewrite sym $ maximumAssociative b a c in
  rewrite sym prf in Refl

maximum_inj : (maximum (S a) (S b) = (S a) -> Void) -> (maximum a b = a -> Void)
maximum_inj {a} {b} f prf =
  void $ f (rewrite prf in Refl)

maximum_l_void : (maximum a b = a -> Void) -> maximum a b = b
maximum_l_void {a = Z} {b = b} f = Refl
maximum_l_void {a = (S k)} {b = Z} f = void $ f Refl
maximum_l_void {a = (S k)} {b = (S j)} f =
  let ihPrf = maximum_inj {a = k} {b = j} f
      ih : (maximum k j = j) = maximum_l_void ihPrf
  in rewrite ih in Refl

all_max_ext : {b1, b2 : Bid}
      -> All (\b => MaxL b2 b) bs
      -> maximum (snd b1) (snd b2) = (snd b1)
      -> All (\b => MaxL b1 b) bs
all_max_ext [] prf = []
all_max_ext {bs = x :: _} {b1} (y :: z) prf =
  let (IsMaxL _ x (c ** (d, e))) = y
  in  (IsMaxL b1 x (c ** (maximum_trans d prf, e))) :: all_max_ext z prf

maxBid_ext : {b1, b2 : Bid}
     -> maximum (snd b1) (snd b2) = (snd b1)
     -> MaxBid b2 bs
     -> MaxBid b1 ((label b1) :: bs)
maxBid_ext {b1} {b2} {bs} maxPrf maxbid =
  let (IsMax _ _ maxbidAll) = maxbid
      headPrf = IsMaxL b1 (label b1) (b1 ** (maximumIdempotent (snd b1), Refl))
      tailPrf = all_max_ext maxbidAll maxPrf
  in IsMax b1 ((label b1) :: bs) (headPrf :: tailPrf)

--------------------------------------------------------------------------------

auction : HatchPair n -> DIO L (Labeled L Bid)
auction ([] ** _) = pure $ label ("no bid", 0)
auction (r :: rs ** hatch) =
     do max <- plug $ getMaxBid (r :: rs)
        let max' : Labeled L Bid = hatch max
        printBid max'
        pure max'
  where
    getMaxBid : (r : BidLog (S n))
             -> DIO H (b : Bid ** HighestBid r b)
    getMaxBid (x :: []) =
      do (x' ** prfx) <- unlabel' x
         let elemPrf : Elem (label x') [x] = rewrite prfx in Here
         let maxlemma = (x' ** (maximumIdempotent (snd x'), prfx))
         let maxPrf : MaxBid x' [x] = IsMax x' [x] ((IsMaxL x' x maxlemma) :: Nil)
         pure (x' ** (elemPrf, maxPrf))
    getMaxBid (x :: y :: zs) =
      do (x' ** prfx) <- unlabel' x
         (tail' ** (prftailElem, prftailMax)) <- getMaxBid (y :: zs)
         let (IsMax _ _ tailprfAll) = prftailMax
         case decEq (maximum (snd x') (snd tail')) (snd x') of
           Yes prf => pure (x' ** (rewrite prfx in Here, rewrite sym prfx in maxBid_ext prf prftailMax))
           No cont => pure (tail' ** (There prftailElem, IsMax tail' (x :: y :: zs)
             ((IsMaxL tail' x (x' ** (
             rewrite maximumCommutative (snd tail') (snd x') in maximum_l_void {b=(snd tail')} cont, prfx))) :: tailprfAll)))

--------------------------------------------------------------------------------
-- TCB
--------------------------------------------------------------------------------
main : IO ()
main =
  do putStrLn "##### Welcome to the auction! #####"
     putStrLn "Announcing winner: "
     max <- run $ auction aHatchPair
     putStrLn "##### Bye bye! #####"
     pure ()
