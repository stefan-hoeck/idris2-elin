module Syntax.E1

import public Data.Linear.ELift1

%default total

export %inline
map1 : (a -> b) -> E1 s es a -> E1 s es b
map1 f g t =
 let R v t := g t | E e t => E e t
  in R (f v) t

export %inline
(<$>) : (a -> b) -> E1 s es a -> E1 s es b
(<$>) = map1

export %inline
(<&>) : E1 s es a -> (a -> b) -> E1 s es b
(<&>) = flip map1

export %inline
ignore1 : E1 s es a -> E1' s es
ignore1 f t =
 let R _ t := f t | E e t => E e t
  in R () t

export %inline
pure : a -> E1 s es a
pure = R

export %inline
(>>=) : E1 s es a -> (a -> E1 s es b) -> E1 s es b
(>>=) f g t1 =
 let R v t2 := f t1 | E e t2 => E e t2
  in g v t2

export %inline
(>>) : E1' s es -> E1 s es b -> E1 s es b
(>>) f g = E1.(>>=) f (\(),t => g t)

export %inline
(<*) : E1 s es b -> E1' s es -> E1 s es b
(<*) f g t =
  let R v t := f t | E e t => E e t
      R _ t := g t | E e t => E e t
   in R v t

export %inline
(<*>) : E1 s es (a -> b) -> E1 s es a -> E1 s es b
(<*>) f g = E1.do
  fn <- f
  v  <- g
  pure (fn v)
