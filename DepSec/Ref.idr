module DepSec.Ref

import public DepSec.Labeled
import public DepSec.DIO
import Data.IORef

%access export

||| Secure reference
data SecRef : (l : labelType) -> (valueType : Type) -> Type where
  ||| TCB
  MkSecRef : (ref : IORef a) -> SecRef l a

||| Create a reference with a labeled intial value
||| @ flow evidence that l may flow to l'
||| @ flow' evidence that l' may flow to l''
||| @ value initial value
newRef : Poset labelType
      => {l, l', l'' : labelType}
      -> {auto flow : l `leq` l'}
      -> {auto flow' : l' `leq` l''}
      -> (value : Labeled l' a)
      -> DIO l (SecRef l'' a)
newRef (MkLabeled v)
  = lift $ newIORef v >>= pure . MkSecRef

||| Read a secure reference
||| @ flow evidence that l may flow to l'
||| @ ref reference to read
readRef : Poset labelType
       => {l, l' : labelType}
       -> {auto flow : l `leq` l'}
       -> (ref  : SecRef l' a)
       -> DIO l (Labeled l' a)
readRef (MkSecRef ioRef)
  = lift $ map MkLabeled $ readIORef ioRef

||| Write a labeled value to a secure reference
||| @ flow evidence that l may flow to l'
||| @ flow' evidence that l' may flow to l''
||| @ ref reference to write to
||| @ content value to write to reference
writeRef : Poset labelType
        => {l, l', l'' : labelType}
        -> {auto flow : l `leq` l'}
        -> {auto flow' : l' `leq` l''}
        -> (ref : SecRef l'' a)
        -> (content : Labeled l' a)
        -> DIO l ()
writeRef (MkSecRef ioRef) (MkLabeled content)
  = lift $ writeIORef ioRef content
