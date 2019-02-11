module DepSec.File

import public DepSec.DIO
import public DepSec.Labeled

%access export

||| Secure file
data SecFile : {label : Type} -> (l : label) -> Type where
  ||| TCB
  MkSecFile : (path : String) -> SecFile l

||| Make a secure file from string
||| TCB
||| @ path path to file
makeFile : (path : String) -> SecFile l
makeFile = MkSecFile

||| Read a secure file
||| @ flow evidence that l may flow to l'
||| @ file secure file to read
readFile : Poset labelType
        => {l,l' : labelType}
        -> {auto flow : l `leq` l'}
        -> (file : SecFile l')
        -> DIO l (Labeled l' (Either FileError String))
readFile (MkSecFile path) = lift $ map MkLabeled $ readFile path

||| Write to a secure file
||| @ file secure file to write to
||| @ flow evidence that l may flow to l'
||| @ flow' evidence that l' may flow to l''
||| @ content labeled content to write
writeFile : Poset labelType
         => {l,l',l'' : labelType}
         -> {auto flow : l `leq` l'}
         -> (file : SecFile l'')
         -> {auto flow' : l' `leq` l''}
         -> (content : Labeled l' String)
         -> DIO l (Labeled l'' (Either FileError ()))
writeFile (MkSecFile path) (MkLabeled content)
  = lift $ map MkLabeled $ writeFile path content
