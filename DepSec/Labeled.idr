module DepSec.Labeled

import public DepSec.DIO
import public DepSec.Poset

%access public export

||| Labeled value
||| @ label label
||| @ valueType type of labeled value
data Labeled : (label : labelType)
            -> (valueType : Type)
            -> Type where
  ||| TCB
  MkLabeled : valueType -> Labeled label valueType

||| Label a value
||| @ value value to label
label : Poset labelType
     => {l : labelType}
     -> (value : a)
     -> Labeled l a
label = MkLabeled

||| Upgrade the security level of a labeled value
||| @ flow evidence that l may flow to l'
||| @ labeled labeled value to relabel
relabel : Poset labelType
       => {l, l' : labelType}
       -> {auto flow : l `leq` l'}
       -> (labeled : Labeled l a)
       -> Labeled l' a
relabel (MkLabeled x) = MkLabeled x

||| Unlabel a labeled value
||| @ flow evidence that l may flow to l'
||| @ labeled labeled value to unlabel
unlabel : Poset labelType
       => {l,l' : labelType}
       -> {auto flow : l `leq` l'}
       -> (labeled : Labeled l a)
       -> DIO l' a
unlabel (MkLabeled val) = pure val

||| Unlabel a labeled value while retaining a proof of relationship
||| @ flow evidence that l may flow to l'
||| @ labeled labeled value to unlabel
unlabel' : Poset labelType
        => {l,l' : labelType}
        -> {auto flow : l `leq` l'}
        -> (labeled : Labeled l a)
        -> DIO l' (c : a ** label c = labeled)
unlabel' (MkLabeled x) = pure (x ** Refl)

||| Plug a secure computation into a less secure computation
||| @ flow evidence that l may flow to l'
||| @ dio secure computation to plug
plug : Poset labelType
    => {l,l' : labelType}
    -> (dio : DIO l' a)
    -> {auto flow : l `leq` l'}
    -> DIO l (Labeled l' a)
plug dio = lift . run $ dio >>= pure . MkLabeled
