module Examples.Declassification.DatingSystem

import Pruviloj.Disjoint

import DepSec.Labeled
import DepSec.DIO
import DepSec.Declassification

import Examples.AuthorityLattice

%language ElabReflection

%default total

data Gender : Type where
 Unknown : Gender
 M : Gender
 F : Gender

implementation DecEq Gender where
  decEq Unknown Unknown = Yes Refl
  decEq Unknown M = No (%runElab disjoint)
  decEq Unknown F = No (%runElab disjoint)
  decEq M Unknown = No (%runElab disjoint)
  decEq M M = Yes Refl
  decEq M F = No (%runElab disjoint)
  decEq F Unknown = No (%runElab disjoint)
  decEq F M = No (%runElab disjoint)
  decEq F F = Yes Refl

record ProfileInfo (Owner : Principal) where
  constructor MkProfileInfo
  name      : Labeled Owner String
  gender    : Labeled Owner Gender
  birthdate : Labeled Owner String
  interests : Labeled Owner String
  city      : Labeled Owner String

DiscoveryResult : Principal -> Type
DiscoveryResult = ProfileInfo

Discoverer : Type
Discoverer = {bOwner : Principal}
          -> (b : ProfileInfo bOwner)
          -> DIO bOwner (Maybe (DiscoveryResult bOwner))

record Profile (Owner : Principal) where
  constructor MkProfile
  info       : ProfileInfo Owner
  discoverer : Discoverer

data GenProfile : (Principal : Type) -> Type where
  MkGenProfile : {t : Principal} -> Profile t -> GenProfile Principal

data Authority : a -> Type where
  ||| TCB
  MkAuthority : (t : a) -> Authority t

authorityHatch : { l, l' : Principal }
              -> (s ** (l = s, Authority s)) -> Labeled l a -> Labeled l' a
authorityHatch {l} = tokenHatch (\s => (l=s, Authority s))

--------------------------------------------------------------------------------
-- Convenience
--------------------------------------------------------------------------------
%hint
hint1 : {a : Principal} -> leq a a
hint1 {a} = reflexive a

implicit
genderToString : Gender -> String
genderToString M = "Male"
genderToString F = "Female"
genderToString Unknown = "Unknown"

implicit
profileToString : (p : DiscoveryResult viewer) -> DIO viewer String
profileToString (MkProfileInfo name gender birthdate likes location) =
   pure ("NAME: "      ++ !(unlabel name) ++ "\n" ++
         "BIRTHDATE: " ++ !(unlabel birthdate) ++ "\n" ++
         "LIKES: "     ++ !(unlabel likes) ++ "\n" ++
         "LOCATION: "  ++ !(unlabel location) ++ "\n")

implicit
toLabeled : Poset labelType => {l : labelType} -> String -> Labeled l String
toLabeled x = label x

implicit
toLabeledG : Poset labelType => {l : labelType} -> Gender -> Labeled l Gender
toLabeledG x = label x

--------------------------------------------------------------------------------
-- UTCB
--------------------------------------------------------------------------------
sampleDiscoverer : {A, B : Principal}
                -> Authority A
                -> (a : ProfileInfo A)
                -> (b : ProfileInfo B)
                -> DIO B (Maybe (DiscoveryResult B))
sampleDiscoverer {A} {B} auth a b =
  do bGender <- unlabel $ gender b
     aGender <- unlabel $ authorityHatch (A ** (Refl, auth)) (gender a)
     aName <- unlabel $ authorityHatch (A ** (Refl, auth)) (name a)
     case decEq bGender aGender of
       Yes prf => pure Nothing
       No contra =>
         let result : DiscoveryResult B = MkProfileInfo (label aName) (label Unknown) "" "" ""
         in pure $ Just result

--------------------------------------------------------------------------------
-- TCB
--------------------------------------------------------------------------------
profileBob : Profile Bob
profileBob =
  let profileInfo = MkProfileInfo "Bob" M "1994" "Nothing" "Aarhus"
  in MkProfile profileInfo (sampleDiscoverer (MkAuthority Bob) profileInfo)

profileAlice : Profile Alice
profileAlice =
  let profileInfo = MkProfileInfo "Alice" F "1993" "Hunting" "Aarhus"
  in MkProfile profileInfo (sampleDiscoverer (MkAuthority Alice) profileInfo)

profileChuck : Profile Chuck
profileChuck =
  let profileInfo = MkProfileInfo "Chuck" M "1992" "Swimming" "Ribe"
  in  MkProfile profileInfo (sampleDiscoverer (MkAuthority Chuck) profileInfo)

profileQueueAlice : List (GenProfile Principal)
profileQueueAlice = [MkGenProfile profileBob, MkGenProfile profileChuck]

printAlice : String -> DIO Alice ()
printAlice x = lift $ putStrLn x

runThroughQueueAlice : (acc : DIO Alice ()) -> List (GenProfile Principal) -> DIO Alice ()
runThroughQueueAlice acc [] = acc
runThroughQueueAlice acc ((MkGenProfile p) :: xs) =
  let thisProfilePrint : DIO Alice ()
    = do acc
         result <- (discoverer p) (info profileAlice)
         case result of
           Nothing => printAlice "Did not wanna be seen"
           Just result' => printAlice !result'
  in runThroughQueueAlice thisProfilePrint xs

main : IO ()
main =
  do putStrLn "########## Alice's queue is checked ##########\n"
     run $ runThroughQueueAlice (pure ()) profileQueueAlice
     putStrLn "########## Done checking ##########"
     pure ()
