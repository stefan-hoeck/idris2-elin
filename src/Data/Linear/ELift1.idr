module Data.Linear.ELift1

import public Data.Linear.Token
import public Control.Monad.MErr

%default total

||| Result of a linear computation running in state thread
||| `s` producing either a value of type `a` or an error of
||| one of the types listed in `es`.
public export
data ERes : (s : Type) -> (es : List Type) -> (a : Type) -> Type where
  E : HSum es   -> (1 t : T1 s) -> ERes s es a
  R : (val : a) -> (1 t : T1 s) -> ERes s es a

||| An alias similar to `F1 s a` but for linear computations that could
||| fail with one of the errors listed.
public export
0 E1 : Type -> List Type -> Type -> Type
E1 s es a = (1 t : T1 s) -> ERes s es a

||| Replaces all errors with `neutral`, running an `E1` as an `F1`.
export %inline
toF1 : Monoid a => E1 s es a -> F1 s a
toF1 act t =
  case act t of
    E _ t => neutral # t
    R v t => v # t

export
mapPRes : (a -> b) -> (1 _ : ERes e es a) -> ERes e es b
mapPRes f (E x t) = E x t
mapPRes f (R v t) = R (f v) t

export
pattempt : (1 r : ERes e es a) -> ERes e fs (Result es a)
pattempt (E x t) = R (Left x) t
pattempt (R v t) = R (Right v) t

export
toResult : (1 r : ERes s es a) -> R1 s (Result es a)
toResult (E x t) = Left x # t
toResult (R v t) = Right v # t

||| An interface for lifting stateful, linear computation into
||| a monad with the potential of failure.
public export
interface MErr f => ELift1 (0 s : Type) f | f where
  elift1 : E1 s es a -> f es a

export %inline
ELift1 s f => Lift1 s (f es) where
  lift1 act = elift1 $ \t => let v # t := act t in R v t

||| Convenience alias for `ELift1 World`
public export
0 EIO1 : (f : List Type -> Type -> Type) -> Type
EIO1 = ELift1 World
