{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}

{-|
  Code from:
  Type Classes with Functional Dependencies
  By: Mark P. Jones
  Link: https://link.springer.com/chapter/10.1007/3-540-46425-5_15

  Using this paper wanted to learn multi parameter type clasess
  and functional dependencies. This paper describes general approach
  how functional dependencies from Data bases theory could be used to
  remove ambigiouty of MultiParamTypeClasses.

  Also there is code from:
  Fun with Funtional Dependenies
  By: Thomas Hallgren
  Link: https://userpages.uni-koblenz.de/~laemmel/TheEagle/dl/Hallgren01.pdf

  This paper describes techniques to do static computations, some involves
  MultiParamTypeClasses and FunctionalDependencies
-}

module FunctionalDependencies where

import           Prelude hiding (even, odd, pred)

-- Multi params represents a relation between two types
-- f :: Eq a => a
-- We say that a is a type with instance Eq
-- g :: TypeClass a b => ...
-- We say that a and b has a relation TypeClass

{-
  -- This typeclass represents a collection
  -- where x is an element and xs is a container
  class Collects x xs where
    empty :: xs
    insert :: x -> xs -> xs
    member :: x -> xs -> Bool

  empty is a bit stange:
  empty :: Collects x xs => xs

  x is ambigiouse, thus GHC whould not compile this term

  insert and member is strange too, consider:
  f x y coll = insert x (insert y coll)
  g coll = f True 'a' coll

  types whould be infered as:
  f :: (Collects x2 xs, Collects x1 xs) => x1 -> x2 -> xs -> xs
  g :: (Collects Bool xs, Collects Char xs) => xs -> xs
  But for GHC you should include
  FlexibleContexts pragma
-}

{-
    Possible solution

    class Collects x xs where
      empty :: xs x
      insert :: x -> xs x -> xs x
      member :: x -> xs x -> Bool

    This is a good fit for 'xs' such as [], it takes unrestricted type-parameter
    and works well.
-}

-- x is determined by xs
class Collects x xs | xs -> x where
  empty :: xs
  insert :: x -> xs -> xs
  member :: x -> xs -> Bool

class Add a b c | a b -> c where
  plus :: a -> b -> c

instance Add Int Int Int where
  plus a b = a + b

-- requires FlexibleInstances
instance Eq a => Collects a [a] where
  empty = []
  insert x xs = x:xs
  member = elem

-- instance Collects Int [Int] where will cause overlapping instances

-- fm - container; i - index; e - elem
class FiniteMap fm i e | fm -> i e where
  emptyFM :: fm
  find :: i -> fm -> Maybe e
  extend :: i -> e -> fm -> fm

instance Eq i => FiniteMap [(i, e)] i e where
  emptyFM = []
  find = lookup
  extend i e fm = (i, e):fm  -- not the best implementation, but good enough for testing

{-
  It is possible to do
  class C a b where . . .
  class D a b | a -> b where . . .
  class E a b | a -> b, b -> a where . . .
-}

data Zero
data Succ n

type Three = Succ (Succ (Succ Zero))

class Even n where isEven :: n
class Odd n where isOdd :: n

instance Even Zero
instance Odd n => Even (Succ n)
instance Even n => Odd (Succ n)

{-
  we can now use ghci:
  > :t isEven :: Three
  > :t isOdd :: Three
-}

data True
data False

class Even' n b where even :: n -> b
class Odd' n b where odd   :: n -> b

instance             Even' Zero     True
instance Odd' n b => Even' (Succ n) b

instance              Odd' Zero     False
instance Even' n b => Odd' (Succ n) b

{-
  Queries:
  > :t odd (undefined :: Three) :: True
  > :t odd (undefined :: Three) :: False

  > :t even (undefined :: Three) :: True
  > :t even (undefined :: Three) :: False

  > :t even (undefined::Three)
  > :t odd (undefined::Three)
-}

-- FunctionalDependencies are used here as a function from a to b
-- so for a given type of natural number we can produce Bool
-- and find out if the number is even or odd
class EvenF n b | n -> b where evenF :: n -> b
class OddF  n b | n -> b where oddF  :: n -> b

-- requires UndecidableInstances
instance             EvenF Zero     True
instance OddF n b => EvenF (Succ n) b

instance              OddF Zero     False
instance EvenF n b => OddF (Succ n) b

{-
  Queries:
  > :t oddF (undefined :: Three)
  > :t evenF (undefined :: Three)
-}

-- Add class defined earlier
instance              Add Zero     b b
instance Add a b c => Add (Succ a) b (Succ c)

class Mult a b c | a b -> c where mul :: a -> b -> c

instance Mult Zero b Zero
instance (Mult a b c, Add b c d) => Mult (Succ a) b d

u = undefined

{-
  Queries:
  > :t plus (u::Three) (u::Three)
  > :t mul  (u::Three) (u::Three)
-}

type One = Succ Zero

class Pow a b c | a b -> c where pow :: a -> b -> с

instance Pow a Zero One
instance (Pow a b c, Mult a c d) => Pow a (Succ b) d

{-
  Queries:
  > :t pow (u::Three) (u::Three)
-}

{-
  This is how we can mix static calculation with dinamic
-}
class Pred a b | a -> b where pred :: a -> b

instance Pred (Succ n) n

class Power n where power :: Int -> n -> Int
instance Power Zero where power _ _ = 1
instance Power n => Power (Succ n) where
  power x n = x * power x (pred n)

{-
  Queries:
  > power 2 (u::Three)
  > power 2 (mul (u::Three) (u::Three))

  - computes mul (u::Three) (u::Three) in compile time
  - produces a power that for given n computes n ^ 9
  - power is computed at the runtime
-}
