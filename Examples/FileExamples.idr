module Examples.FileExamples

import Data.List

import DepSec.DIO
import DepSec.Labeled
import DepSec.File

import Examples.TwoPointLattice as TPL
import Examples.FourPointLattice as FPL

%default total

--------------------------------------------------------------------------------
-- Bob/library, untrusted
--------------------------------------------------------------------------------

||| Generic file for keeping files of diffent level in same datastructure
GenFile : Type -> Type
GenFile label = (l : label ** SecFile l)

annotateStr : Either FileError String -> String
annotateStr (Left error) = "Deduced information that no file with this name existed"
annotateStr (Right str) = str ++ "\n The above was annotated by Bob."

annotateFile : Poset labelType
            => {l : labelType}
            -> (file: SecFile l)
            -> DIO l ()
annotateFile {l} file =
  do labeledSecContent <- readFile {flow = reflexive l} file
     secComp <- unlabel {flow = reflexive l} labeledSecContent
     let labeledSecret = label $ annotateStr secComp
     writeFile {flow = reflexive l} {flow' = reflexive l} file labeledSecret
     pure ()

moveContent : Poset labelType
           => {l, l' : labelType}
           -> {auto flowup : l `leq` l'}
           -> (source: SecFile l)
           -> (dest: SecFile l')
           -> DIO l ()
moveContent {flowup} {l} {l'} source dest =
  do labeledSecContent <- readFile {flow = reflexive l} source
     secComp <- unlabel {flow = reflexive l} labeledSecContent
     let labeledSecret = label $ annotateStr secComp
     writeFile {flow = flowup} {flow' = reflexive l'} dest labeledSecret
     pure ()

||| Read two files to join
readTwoFiles : BoundedJoinSemilattice label
            => {l, l' : label}
            -> SecFile l
            -> SecFile l'
            -> DIO (Bottom {a=label}) (Labeled (join l l') (Either FileError String))
readTwoFiles file1 file2 {l} {l'} =
  do file1' <- readFile {flow = leq_bot_x l} file1
     file2' <- readFile {flow = leq_bot_x l'} file2
     let dio : DIO (join l l') (Either FileError String)
       = do c1 <- unlabel {flow = join_x_xy l l'} file1'
            c2 <- unlabel {flow = join_y_xy l l'} file2'
            pure $ case (c1, c2) of
                        (Right c1', Right c2') => Right $ c1' ++ c2'
                        (Left e1, _) => Left e1
                        (_, Left e2) => Left e2
     plug {flow = leq_bot_x (join l l')} dio

||| Get list of labels from list of files.
getLabels : List (GenFile labelType) -> List labelType
getLabels [] = []
getLabels ((l ** _) :: files) = l :: getLabels files

||| Get total join of a list of labels.
getJoinOfLabels : BoundedJoinSemilattice labelType => List labelType -> labelType
getJoinOfLabels [] = Bottom
getJoinOfLabels (x :: xs) = join x (getJoinOfLabels xs)

||| Get join of security levels from a list of files.
joinOfFiles : BoundedJoinSemilattice label => List (GenFile label) -> label
joinOfFiles xs = getJoinOfLabels $ getLabels xs

||| Convenient helper function for converting Either FileError String to String.
getString : Either FileError String -> String
getString (Left error) = "----Missing file----\n"
getString (Right str) = str ++ "\n"

||| Convenient helper function for concatenating content of same level.
addContent : DIO l String
          -> DIO l (Either FileError String)
          -> DIO l String
addContent accDIO newDIO = do pure $ !accDIO ++ (getString !newDIO)

addContent' : DIO l (Either (List FileError) String)
           -> DIO l (Either FileError String)
           -> DIO l (Either (List FileError) String)
addContent' c1 c2 =
  do pure $ case (!c1, !c2) of
                 (Right c1', Right c2') => Right $ c1' ++ c2'
                 (Left e1, Left e2) => Left $ e2 :: e1
                 (Left e1, Right c1) => Left e1
                 (Right c1', Left e2) => Left [e2]

||| A type which describes that a list is a sublist of another list
data SubOrEqualList : List a -> List a -> Type where
  Base : SubOrEqualList list list
  Greater : (prf: SubOrEqualList xs bs) -> SubOrEqualList xs (b::bs)

||| A proof that if a l is allowed to flow to join of sublist then it can flow to join of superlist as well
total subSuperListFlow : BoundedJoinSemilattice lt
                      => (l : lt)
                      -> (superList : List lt)
                      -> (subList : List lt)
                      -> (setPrf : SubOrEqualList subList superList)
                      -> (flowPrf : l `leq` (getJoinOfLabels subList))
                      -> l `leq` (getJoinOfLabels superList)
subSuperListFlow l [] [] x flowPrf = flowPrf
subSuperListFlow _ [] (_ :: _) Base _ impossible
subSuperListFlow _ [] (_ :: _) (Greater _) _ impossible
subSuperListFlow l (z :: xs) (z :: xs) Base flowPrf = flowPrf
subSuperListFlow l (z :: xs) subList (Greater prf) flowPrf =
  let proofOfSubList  = subSuperListFlow l xs subList prf flowPrf
      nearlyThere = join_x_xy (getJoinOfLabels xs) z
      evenBetter: leq (getJoinOfLabels xs) (join z (getJoinOfLabels xs))
        = rewrite commutative z (getJoinOfLabels xs) in nearlyThere
  in transitive l (getJoinOfLabels xs) (join z (getJoinOfLabels xs)) proofOfSubList evenBetter

||| Function for constructing a proof that a list is sublist or equal to itself.
buildSubList : (list : List a) -> SubOrEqualList list list
buildSubList list = Base

||| Function for constructing a proof that if (x::xs) is sublist then xs will be a sublist as well.
buildSubListProf : (subsetProf: SubOrEqualList (x::xs) list)
               -> SubOrEqualList xs list
buildSubListProf Base = Greater Base
buildSubListProf (Greater prf) = Greater (buildSubListProf prf)

||| Proof that a specific label in a list of labels is allowed to flow to join of that list.
||| @l the label which we want a proof for.
||| @list the list of labels.
||| @prf a proof that l is in the list.
total listElemProver : BoundedJoinSemilattice lt
                    => (l : lt)
                    -> (list : List lt)
                    -> {auto prf :Elem l list}
                    -> leq l (getJoinOfLabels list)
listElemProver _ [] {prf = Here} impossible
listElemProver _ [] {prf = There _} impossible
listElemProver _ (z :: xs) {prf = Here} =
  join_x_xy z (getJoinOfLabels xs)
listElemProver l (z :: xs) {prf = (There later)} =
  let flowTail = listElemProver l xs
      help = join_x_xy (getJoinOfLabels xs) z
      nearlyThere = transitive l (getJoinOfLabels xs) (join (getJoinOfLabels xs) z) flowTail help
  in rewrite (commutative z (getJoinOfLabels xs)) in nearlyThere

readFiles : BoundedJoinSemilattice a
         => (files: (List (GenFile a)))
         -> DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String))
readFiles {a} files
  = let initialAcc : DIO Bottom (Labeled (joinOfFiles files) (Either (List FileError) String))
      = pure $ label $ Right ""
    in readFilesAcc files initialAcc

  where
  readFilesAcc : (trailingList : List (GenFile a))
              -> {auto subsetProf: SubOrEqualList (getLabels trailingList) (getLabels files)}
              -> (acc : DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String)))
              -> DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String))
  readFilesAcc [] acc = acc
  readFilesAcc {subsetProf} ((l ** file) :: xs) acc =
    do labeledNewContent <- readFile file {flow = leq_bot_x l}
       let subsetProofy : leq l (joinOfFiles ((l ** file) :: xs))
         = listElemProver {prf = Here} l (getLabels ((l ** file) :: xs))
       let trueProof : leq l (joinOfFiles files)
         = subSuperListFlow l (getLabels files)
                            (getLabels ((l ** file) :: xs)) subsetProf subsetProofy
       let content : DIO (joinOfFiles files) (Either FileError String)
         = unlabel {flow = trueProof} labeledNewContent
       let dioAcc : DIO (joinOfFiles files) (Either (List FileError) String)
         = unlabel !acc {flow = reflexive (joinOfFiles files)}
       let newDIOAcc : DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String))
         = plug {flow = leq_bot_x (joinOfFiles files)} $ addContent' dioAcc content
       readFilesAcc {subsetProf = (buildSubListProf subsetProf)} xs newDIOAcc

readFiles' : BoundedJoinSemilattice a => DecEq a => (files: (List (GenFile a)))
          -> DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String))
readFiles' {a} files
  = readFilesAcc files $ pure $ label $ Right ""
  where
  readFilesAcc : (trailingList : List (GenFile a))
              -> (acc : DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String)))
              -> DIO (Bottom {a}) (Labeled (joinOfFiles files) (Either (List FileError) String))
  readFilesAcc [] acc = acc
  readFilesAcc ((l ** file) :: xs) acc =
    case decLeq l (joinOfFiles files) of --JIF actsfor check.
      Yes prf =>
        do labeledNewContent <- readFile file {flow = leq_bot_x l}
           let content = unlabel {flow = prf} labeledNewContent
           let uacc  = unlabel !acc {flow = reflexive (joinOfFiles files)}
           let acc' = plug {flow = leq_bot_x (joinOfFiles files)} $ addContent' uacc content
           readFilesAcc xs acc'
      No _ => acc -- Never gonna happen.

||| Reads all files of certain level to a string of that particular level.
readAllFilesOfLevel : BoundedJoinSemilattice lt
                   => DecEq lt
                   => (level: lt)
                   -> (list: List (GenFile lt))
                   -> DIO (Bottom {a = lt}) (Labeled level String)
readAllFilesOfLevel {lt} level list =
  let init : DIO (Bottom {a = lt}) (Labeled level String) = pure $ label ""
  in readSameLevelFiles (createListOfSameLevel list []) init

  where
  readSameLevelFiles : (list' : List (SecFile level))
                    -> (acc: DIO (Bottom {a = lt}) (Labeled level String))
                    -> DIO (Bottom {a = lt}) (Labeled level String)
  readSameLevelFiles [] acc = acc
  readSameLevelFiles (file :: xs) acc
    = do labeledNewContent <- readFile file {flow = (leq_bot_x level)}
         let content : DIO level (Either FileError String)
           = unlabel labeledNewContent {flow = reflexive level}
         let dioAcc : DIO level String
           = unlabel !acc {flow = reflexive level}
         let newDIOAcc : DIO (Bottom {a = lt}) (Labeled level String)
           = plug {flow = (leq_bot_x level)} $ addContent dioAcc content
         readSameLevelFiles xs newDIOAcc

  createListOfSameLevel : (list' : List (GenFile lt))
                       -> (acc : List (SecFile level))
                       -> List (SecFile level)
  createListOfSameLevel [] acc = acc
  createListOfSameLevel ((l ** file) :: xs) acc
    = case decEq level l of
        Yes Refl => createListOfSameLevel xs (file :: acc)
        No contra => createListOfSameLevel xs acc

||| Read all files below a certain level to a string of that particular level
readAllFilesBelowLevel : BoundedJoinSemilattice a
                      => DecEq a
                      => (list : List (GenFile a))
                      -> (level : a)
                      -> DIO (Bottom {a}) (Labeled level String)
readAllFilesBelowLevel {a} list level =
  readFilesAcc list $ pure $ label ""

  where
  readFilesAcc : (trailingList : List (GenFile a))
              -> (acc : DIO (Bottom {a}) (Labeled level String))
              -> DIO (Bottom {a}) (Labeled level String)
  readFilesAcc [] acc = acc
  readFilesAcc ((l ** file) :: xs) acc =
    case decLeq l level of
      (Yes prf) =>
        do labeledNewContent <- readFile file {flow = (leq_bot_x l)}
           let content : DIO level (Either FileError String)
             = unlabel labeledNewContent {flow = prf}
           let dioAcc : DIO level String
             = unlabel !acc {flow = reflexive level}
           let newDIOAcc : DIO (Bottom {a}) (Labeled level String)
             = plug {flow = leq_bot_x level} $ addContent dioAcc content
           readFilesAcc xs newDIOAcc
      (No contra) => readFilesAcc xs acc

-- Alice, trusted
namespace tp

  secretFile : SecFile TPL.H
  secretFile = makeFile "tpSecretFile.txt"

  publicFile : SecFile TPL.L
  publicFile = makeFile "tpPublicFile.txt"

  listOfFiles : List (GenFile TwoPoint)
  listOfFiles = [(_ ** secretFile), (_ ** publicFile)]

namespace fp
  secretFile : SecFile FPL.H
  secretFile = makeFile "fpSecretFile.txt"

  publicFile : SecFile FPL.L
  publicFile = makeFile "fpPublicFile.txt"

  medium1File : SecFile FPL.M1
  medium1File = makeFile "fpMedium1File.txt"

  medium2File : SecFile FPL.M2
  medium2File = makeFile "fpMedium2File.txt"

  listOfFilesH : List (GenFile FourPoint)
  listOfFilesH = [(_ ** medium1File), (_ ** publicFile), (_ ** medium2File)]

  listOfFilesM1 : List (GenFile FourPoint)
  listOfFilesM1 = [(_ ** medium1File), (_ ** publicFile)]

-- Silent fail on file errors
stringOfEither : BoundedJoinSemilattice a
              => {l : a}
              -> DIO (Bottom {a}) (Labeled l (Either (List FileError) String))
              -> DIO (Bottom {a}) (Labeled l String)
stringOfEither {a} {l} comp =
  do labeled <- comp
     let stringComp : DIO l String =
       do comp' <- unlabel {flow = reflexive l} labeled
          case comp' of
            Left _  => pure ""
            Right b => pure b
     plug {flow = leq_bot_x l} stringComp

main : IO ()
main =
  do putStrLn "Started.."

     -- annotateFile examples
     --------------------------------------------------
     run $ annotateFile tp.secretFile
     run $ annotateFile fp.secretFile

     -- moveContent examples
     --------------------------------------------------
     run $ moveContent {flowup = Refl} tp.publicFile tp.secretFile
     run $ moveContent {flowup = Refl} tp.secretFile tp.secretFile
     -- run $ moveContent tp.secretFile tp.publicFile -- Illegal flow!
     run $ moveContent {flowup = Refl} fp.publicFile fp.secretFile
     run $ moveContent {flowup = Refl} fp.secretFile fp.secretFile
     run $ moveContent {flowup = Refl} fp.medium1File fp.secretFile
     -- run $ moveContent fp.secretFile fp.medium1File -- Illegal flow!
     -- run $ moveContent fp.medium2File fp.medium1File -- Illegal flow!

     --------------------------------------------------
     tpLabeledString <- run $ stringOfEither $ readFiles tp.listOfFiles
     run $ writeFile {l = TPL.L} {flow = leq_bot_x (joinOfFiles tp.listOfFiles)} {flow' = Refl} tp.secretFile $ tpLabeledString
     -- run $ writeFile tp.publicFile tpLabeledString -- Illegal flow!
     fpLabeledStringH <- run $ stringOfEither $ readFiles fp.listOfFilesH
     run $ writeFile {l = FPL.L} {flow = leq_bot_x (joinOfFiles fp.listOfFilesH)} {flow' = Refl} fp.secretFile fpLabeledStringH
     -- run $ writeFile fp.medium1File fpLabeledStringH -- Illegal flow!
     fpLabeledStringM1 <- run $ stringOfEither $ readFiles fp.listOfFilesM1
     run $ writeFile {l = FPL.L} {flow = leq_bot_x (joinOfFiles fp.listOfFilesM1)} {flow' = Refl} fp.secretFile fpLabeledStringM1
     run $ writeFile {l = FPL.L} {flow = leq_bot_x (joinOfFiles fp.listOfFilesM1)} {flow' = Refl} fp.medium1File fpLabeledStringM1
     -- run $ writeFile fp.medium2File fpLabeledStringM1 -- Illegal flow!
     -- run $ writeFile fp.publicFile fpLabeledStringM1 -- Illegal flow!
     putStrLn "Done!"
