module DepSec.Declassification

import DepSec.Labeled

%access export

||| Predicate hatch builder
||| TCB
||| @D data structure type
||| @E element type
||| @d data structure where declassification is allowed from
||| @P predicate
predicateHatch : Poset labelType
             => {l, l' : labelType}
             -> {D, E : Type}
             -> (d : D)
             -> (P : D -> E -> Type)
             -> (d : D ** Labeled l (e : E ** P d e) -> Labeled l' E)
predicateHatch {labelType} {l} {l'} {E} d P = (d ** hatch)
  where
    hatch : Labeled l (e : E ** P d e) -> Labeled l' E
    hatch (MkLabeled (x ** _)) = label x

||| Token hatch builder
||| TCB
||| @E value type
||| @S token type
||| @Q token predicate
tokenHatch : Poset labelType
          => {l, l' : labelType}
          -> {E, S : Type}
          -> (Q : S -> Type) -- 'when'/'who' predicate
          -> (s : S ** Q s) -> Labeled l E -> Labeled l' E
tokenHatch {labelType} {l} {l'} {E} {S} Q = hatch
  where
    hatch : (s : S ** Q s) -> Labeled l E -> Labeled l' E
    hatch _ (MkLabeled x) = label x

||| Generic combined hatch builder
||| TCB
||| @d data structure
||| @Q token predicate
||| @P predicate
hatchBuilder : Poset labelType
            => {l, l' : labelType}
            -> {D, E, S : Type}
            -> (d : D) -- datastructre
            -> (Q : S -> Type) -- 'when'/'who' predicate
            -> (P : D -> E -> Type) -- 'what' predicate
            -> (d : D ** Labeled l (e :  E ** P d e) -> (s : S ** Q s) -> Labeled l' E)
hatchBuilder {labelType} {l} {l'} {E} {S} d Q P =  (d ** hatch)
  where
    hatch : Labeled l (e : E ** P d e) -> (s : S ** Q s) -> Labeled l' E
    hatch (MkLabeled (x ** _)) _ = label x
