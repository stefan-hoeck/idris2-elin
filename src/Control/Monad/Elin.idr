module Control.Monad.Elin

import public Control.Monad.HErr
import public Data.Linear.ELift1

%default total

||| A monad for running pure, stateful computations in
||| state thread `s` with the potential of failing with one
||| of the errors listed in `es`.
public export
record Elin (s : Type) (es : List Type) (a : Type) where
  constructor E
  run : E1 s es a

bindImpl : Elin s es a -> (a -> Elin s es b) -> Elin s es b
bindImpl (E g) f =
  E $ \t => case g t of
    E x t => E x t
    R v t => run (f v) t

export %inline
MErr (Elin s) where
  fail x    = E (E x)
  succeed v = E (R v)
  bind      = bindImpl
  attempt x = E $ \t => pattempt (run x t)

export %inline
ELift1 s (Elin s) where
  elift1 = E

export %inline
HasIO (Elin World es) where
  liftIO = lift1 . ioToF1

||| When universally quantified over `s`, the `Elin` monad can
||| be run to produce a pure value of type `Result es a`, even though
||| running the value might involve working with freshly allocated
||| mutable state.
export %inline
runElin : (forall s . Elin s es a) -> Result es a
runElin p = run1 $ \t => toResult (p.run t)

||| When tagged with `World`, the `Elin` monad is just `IO` plus
||| error handling.
export %inline
runElinIO : Elin World es a -> IO (Result es a)
runElinIO p = runIO $ \t => toResult (p.run t)
