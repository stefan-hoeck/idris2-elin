module Control.Monad.MErr

import public Data.List.Quantifiers.Extra

%default total

||| Generalized result of running a pure computation with
||| error handling: Possible error values are wrapped in
||| a heterogeneous sum.
public export
0 Result : List Type -> Type -> Type
Result es a = Either (HSum es) a

||| A monad with error handling via a generalized bind
|||
||| Possible errors are given as a `List Type` parameter, and a single
||| error is wrapped in an `HSum`.
public export
interface MErr (0 m : List Type -> Type -> Type) where
  fail    : HSum es -> m es a
  succeed : a -> m es a
  attempt : m es a -> m fs (Result es a)
  bind    : m es a -> (a -> m es b) -> m es b
  mapImpl : (a -> b) -> m es a -> m es b
  appImpl : m es (a -> b) -> m es a -> m es b

public export %inline
MErr m => Functor (m es) where
  map = mapImpl

public export %inline
MErr m => Applicative (m es) where
  pure  = succeed
  (<*>) = appImpl

public export %inline
MErr m => Monad (m es) where
  (>>=) = bind

export %inline
fromResult : MErr m => Result es a -> m es a
fromResult = either fail succeed

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| Throws a single error by injecting it into the sum of possible errors.
export %inline
throw : MErr m => Has x es => x -> m es a
throw = fail . inject

||| Inject an `Either e a` computation into an `Async` monad dealing
||| with several possible errors.
export
injectEither : MErr m => Has x es => Either x a -> m es a
injectEither (Left v)  = throw v
injectEither (Right v) = succeed v

||| Handle possible errors with the given function
export
handleErrors : MErr m => (HSum es -> m fs a) -> m es a -> m fs a
handleErrors f act = attempt act >>= either f pure

||| Tries to extract errors of a single type from a computation that
||| can fail wrapping it in a `Left`. Other errors will be rethrown.
export
catch : MErr m => (0 e : Type) -> Has e es => m es a -> m es (Either e a)
catch e m =
  attempt m >>= \case
    Right v   => pure $ Right v
    Left errs => case project e errs of
      Nothing  => fail errs
      Just err => pure $ Left err

||| Tries to extract errors of a single type from a computation that
||| can fail wrapping it in a `Left`. Other errors will be rethrown.
|||
||| Unlike `catch`, this will decompose the list of possible errors,
||| so errors can be handled one type at a time.
export
extractErr : MErr m => (0 e : Type) -> (p : Has e es) => m es a -> m (es - e) (Either e a)
extractErr e m =
  attempt {fs = es - e} m >>= \case
    Right v   => pure $ Right v
    Left errs => case decomp @{p} errs of
      Left x   => fail x
      Right x  => pure $ Left x

export %inline
mapErrors : MErr m => (HSum es -> HSum fs) -> m es a -> m fs a
mapErrors f = handleErrors (fail . f)

widen_ : All (`Elem` es) fs => HSum fs -> HSum es
widen_ @{_::_} (Here v)  = inject v
widen_ @{_::_} (There v) = widen_ v

export %inline
widenErrors : MErr m => All (`Elem` es) fs => m fs a -> m es a
widenErrors = mapErrors widen_

export %inline
weakenErrors : MErr m => m [] a -> m fs a
weakenErrors = handleErrors absurd

export %inline
dropErrs : MErr m => m es () -> m [] ()
dropErrs = handleErrors (const $ succeed ())

export %inline
liftError : MErr m => m [e] a -> m fs (Either e a)
liftError = handleErrors (pure . Left . project1) . map Right

export %inline
handle : MErr m => All (\e => e -> m [] a) es -> m es a -> m [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

||| Sequencing of computations plus error handling
export %inline
bindResult : MErr m => m es a -> (Result es a -> m fs b) -> m fs b
bindResult act f = attempt act >>= f

||| Runs the given handler in case of an error but does not
||| catch the error in question.
export %inline
onError : MErr m => m es a -> (HSum es -> m [] ()) -> m es a
onError act f = handleErrors (\x => weakenErrors (f x) >> fail x) act

||| Handles the given error by replacing it with the provided value.
|||
||| All other errors will be unaffected.
export
ifError : MErr m => Has e es => Eq e => (err : e) -> Lazy a -> m es a -> m es a
ifError err v =
  handleErrors $ \x => case project e x of
    Nothing => fail x
    Just y  => if err == y then pure v else fail x
