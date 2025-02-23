module Control.Monad.Resource

import Control.Monad.MCancel
import Control.Monad.MErr

%default total

public export
interface Resource (0 f : List Type -> Type -> Type) (0 a : Type) | a where
  cleanup : a -> f [] ()

||| Allocate a resource, use it in a program, and make sure to release it
||| afterwards.
export %inline
use1 : MCancel f => Resource f a => f es a -> (a -> f es b) -> f es b
use1 alloc act = bracket alloc act cleanup

||| Like `use1` but for a heterogeneous list of resources.
export
use :
     {auto all : All (Resource f) ts}
  -> {auto can : MCancel f}
  -> (allocs   : All (f es) ts)
  -> (act      : HList ts -> f es b)
  -> f es b
use @{[]}   []     act = act []
use @{_::_} (h::t) act = use1 h (\r => use t (act . (r::)))
