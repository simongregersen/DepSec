module DepSec.DIO

%access public export

||| Security monad
||| @ l security label of wrapped value
||| @ valueType type of wrapped value
data DIO : l
        -> (valueType : Type)
        -> Type where
  ||| TCB
  MkDIO : IO valueType -> DIO l valueType

||| Unwrap security monad
||| TCB
||| @ dio secure computation
run : (dio : DIO l a) -> IO a
run (MkDIO m) = m

||| Lift arbitrary IO monad into security monad
||| TCB
||| @ io computation
lift : (io : IO a) -> DIO l a
lift = MkDIO

Functor (DIO l) where
  map f (MkDIO io) = MkDIO (map f io)

Applicative (DIO l) where
  pure = MkDIO . pure
  (<*>) (MkDIO f) (MkDIO a) = MkDIO (f <*> a)

Monad (DIO l) where
  (>>=) (MkDIO a) f = MkDIO (a >>= run . f)
