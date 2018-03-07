{-# LANGUAGE TypeOperators #-}

{-|
  Code taken from
  Applicative programming with effects
  By: CONOR MCBRIDE, ROSS PATERSON
  Link: https://goo.gl/6Z4Z52

  I found this paper usefull for understanding Applicative, Traversable, Foldable
  typeclasses
-}

module ApplicativeEffects where

import           Prelude hiding (Applicative (..), Monoid (..),
                          Traversable (..), any, fmap, repeat, sequence,
                          sequenceA, traverse)

sequence :: [IO a] -> IO [a]
sequence [] = return []
sequence (c:cs) = do
  x <- c
  xs <- sequence cs
  return (x:xs)

ap :: Monad m => m (a -> b) -> m a -> m b
ap mf mx = do
  f <- mf
  x <- mx
  return $ f x

sequence' :: [IO a] -> IO [a]
sequence' []     = return []
sequence' (c:cs) = return (:) `ap` c `ap` sequence' cs
-- seems like applicative style: f <$> x <*> sequence' xs
-- also could be written as
-- sequence' = foldr (\c -> ap (return (:) `ap` c)) (return [])
-- sequence' (c:cs) = (:) <$> c <*> sequence' cs
-- sequence' (c:cs) = pure (:) <*> c <*> sequence' cs

repeat :: a -> [a]
repeat x = x : repeat x

transpose :: [[a]] -> [[a]]
transpose []       = repeat []
transpose (xs:xss) = zipWith (:) xs (transpose xss)
-- could be rewritten with foldr
-- transpose = foldr (zipWith (:)) (repeat [])

-- family of zipWith could be generated using applicative and repeat
zapp :: [a -> b] -> [a] -> [b]
zapp (f:fs) (x:xs) = f x:zapp fs xs
zapp _ _           = []
-- zipWithN f xs1 .. xsn = repeat f `zapp` xs1 `zapp` ... `zapp` xsn

transpose' :: [[a]] -> [[a]]
transpose' []       = repeat []
transpose' (xs:xss) = repeat (:) `zapp` xs `zapp` transpose xss
-- looks like applicative style too

data Exp v =
  Var v
  | Val Int
  | Add (Exp v) (Exp v)

-- dummy type for example
newtype Env v = Env v
fetch :: v -> Env v -> Int
fetch = undefined

-- for Exp evaluator we should pass Env everywhere
eval :: Exp v -> Env v -> Int
eval (Var v) env   = fetch v env
eval (Val i) _     = i
eval (Add p q) env = eval p env + eval q env

-- This eval is a bit noisy, we can rewrite it as
-- so env passed implicitly
eval' :: Exp v -> Env v -> Int
eval' (Var v)   = fetch v
eval' (Val i)   = combK i
eval' (Add p q) = combK (+) `combS` eval p `combS` eval q
-- looks like applicative style

combK :: a -> Env v -> a -- return of Env Monad
combK x _ = x

combS :: (Env v -> a -> b) -> (Env v -> a) -> Env v -> b -- ap of Env Monad
combS ef es env = ef env (es env)

-- generalisation of combK and combS
-- from threading an environment to threading an effect
infixl 4 <*>
class Applicative f where
  {-|
    Embeds pure computation into the pure fragmenet of an
    effectful world
  -}
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

{-|
                  LAWS
  identity:     pure id <*> u = u
  composition:  pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  homomorphism: pure f <*> pure x = pure (f x)
  interchange:  u <*> pure x = pure (\f -> f x) <*> u
-}

-- Applicative functors are indeed Functors
fmap :: Applicative f => (a -> b) -> f a -> f b
fmap f u = pure f <*> u

{-
  Moreover, any expression built from the Applicative combinators can be transformed
  to a canonical form in which a single pure function is ‘applied’ to the effectful parts
  in depth-first order:
  pure f <*> u1 <*> ... <*> un
-}

{-
  Derive Applicative from Monad:
  pure = reutrn
  (<*>) = ap
-}

-- Now rewrite sequence
sequenceA :: Applicative f => [f a] -> f[a]
sequenceA []     = pure []
sequenceA (c:cs) = pure (:) <*> c <*> sequenceA cs
-- using foldr
-- sequenceA = foldr (\c -> (<*>) (pure (:) <*> c)) (pure [])

type ExpEnv v = (->) v Int -- this is our env

instance Applicative ((->) e) where
  pure = const
  ef <*> ex = \env -> ef env (ex env)

fetch' :: v -> ExpEnv v -> Int
fetch' v env = env v

-- Now rewrite eval
evalA :: Exp v -> ExpEnv v -> Int
evalA (Var x)   = fetch' x
evalA (Val i)   = pure i
evalA (Add p q) = pure (+) <*> evalA p <*> evalA q

-- And we can rewrite transpose with Applicative now
instance Applicative [] where
  pure = repeat
  (<*>) = zapp

transposeA :: [[a]] -> [[a]]
transposeA []       = pure []
transposeA (xs:xss) = pure (:) <*> xs <*> transpose xss

-- now transposeA looks like sequenceA
-- let's generalise it with new func dist

dist' :: Applicative f => [f a] -> f [a]
dist' []     = pure []
dist' (x:xs) = pure (:) <*> x <*> dist' xs

-- Now let's map a function that can produce error over list of argumnents
instance Applicative Maybe where
  pure = Just

  Nothing <*> _ = Nothing
  _ <*> Nothing = Nothing
  Just f <*> Just v = Just $ f v

failMap :: (a -> Maybe a) -> [a] -> Maybe [a]
failMap f xs = dist' (fmap f xs)

-- this failMap applies function to elements of the list
-- than it traverses it again to deside if computation failed
-- we can abstract this using:
traverse' :: Applicative f => (a -> f b) -> [a] -> f [b]
traverse' _ []     = pure []
traverse' f (x:xs) = pure (:) <*> f x <*> traverse' f xs

-- we can abstract traverse and dist even further
class Traversable t where -- in the Prelude dist has name sequence
  traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  dist :: Applicative f => t (f a) -> f (t a)
  dist = traverse id

-- We can recover fmap by setting t as Id

newtype Id a = An { an :: a }

instance Applicative Id where
  pure = An
  An f <*> An v = An $ f v

fmap' :: Traversable t => (a -> b) -> t a -> t b
fmap' f = an . traverse (An . f)

data Tree a = Leaf | Node (Tree a) a (Tree a) deriving Show

instance Traversable Tree where
  traverse _ Leaf         = pure Leaf
  traverse f (Node l v r) = pure Node <*> traverse f l <*> f v <*> traverse f r

instance Traversable [] where
  traverse = traverse'

{-|
  consider (=> evaluation step, maybe not exactly like that, but to provide intuition):
  traverse Just (Node Leaf 1 Leaf) =>
  pure Node <*> traverse Just Leaf <*> Just 1 <*> traverse Just Leaf =>
  pure Node <*> pure Leaf <*> Just 1 <*> pure Leaf => look at pure and <*> for Maybe
  Just Node <*> Just Leaf <*> Just 1 <*> Just Leaf =>
  Just $ Node Leaf <*> Just 1 <*> Just Leaf =>
  Just $ Node Leaf 1 <*> Just Leaf =>
  Just $ Node Leaf 1 Leaf

  So if we give function that can produce Nothing during traversal, traverse will compute Nothing
  due to Applicative Maybe instance
-}

-- <> is a associative operator with identity (mempty), example:
-- + for numbers, mempty = 0
-- * for numbers, mempty = 1
-- ++ for lists, mempty = []
infixr 6 <>
class Monoid a where
  mempty :: a
  (<>) :: a -> a -> a

-- We can induce Applicative instance from Monoid

newtype Accy o a = Acc { acc :: o }

instance Monoid o => Applicative (Accy o) where
  pure _ = Acc mempty
  Acc l <*> Acc r = Acc (l <> r)

newtype Sum a = Sum { getSum :: a }

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  Sum l <> Sum r = Sum (l + r)

-- this function looks like:
-- foldMap :: (Monoid m, Foldable t) => (a -> m) -> t a -> m
accumulate :: (Traversable t, Monoid o) => (a -> o) -> t a -> o
accumulate f = acc . traverse (Acc . f)
-- simmiliar to how we can derived fmap from Applicative
-- example: getSum $ accumulate Sum [1, 2, 3]

reduce :: (Traversable t, Monoid o) => t o -> o
reduce = accumulate id
-- example:
-- l = fmap Sum [1, 2, 3]
-- getSum $ reduce l

{-|
  That accumulate and reduce abstracted via Foldable in Haskell
-}

instance Monoid [a] where
  mempty = []
  (<>) = (++)

-- We can now implelement some functions more easily
flatten :: Tree a -> [a]
flatten = accumulate (:[])

concat :: [[a]] -> [a]
concat = reduce

newtype Mighty = Might { might :: Bool }

-- we can use Monoid for more cool things
instance Monoid Mighty where
  mempty = Might False
  Might p <> Might q = Might (p && q)

any :: Traversable t => (a -> Bool) -> t a -> Bool
any p = might . accumulate (Might . p)

-- elem could be expressed asing Mighty monoid
elem :: (Traversable t, Eq a) => a -> t a -> Bool
elem = any . (==)

{-
  There are more Applicative than Monads
  we can derive Applicative from Monad
  but try to implelement:
  instance Monad (Accy o) where
    return = pure
    (>>=) :: Accy o a -> (a -> Accy o b) -> Accy o b
    Accy p >>= Accy f = ???
  we cannot get 'a' from Accy because it is phantom
-}

-- Monads more powerfull than Applicative
miffy :: Monad m => m Bool -> m a -> m a -> m a
miffy mb mt me = do
  b <- mb
  if b then mt else me

iffy :: Applicative f => f Bool -> f a -> f a -> f a
iffy fb ft fe =
    pure cond <*> fb <*> ft <*> fe
  where
    cond b t e = if b then t else e

-- now run
-- miffy (Just True) (Just 1) Nothing
-- iffy (Just True) (Just 1) Nothing
-- miffy can compute the result even when everything cannot be computed,
-- this provides us somekind of non-determinism

-- The weakness of Applicative provides us ability to compose Applictive functors
-- We cannot compose Monads in general (Barr & Wells, 1984)

-- for <.> we need TypeOperators
newtype (f <.> g) a = Comp { comp :: f (g a) }

-- We just lift inner Applicative operations to the outer layer
instance (Applicative f, Applicative g) => Applicative (f <.> g) where
  pure = Comp . pure . pure
  Comp fs <*> Comp fg = Comp $ pure (<*>) <*> fs <*> fg

-- So compositions of two Monads not always a Monad, but Applicative for sure!
-- Consider Maybe <.> IO and IO <.> Maybe
-- We can achieve both Monad and Applictive by composing IO and Maybe
-- Monad will be able to abort computation if something fails, but Applicative cannot
-- Lets compare errors for Monads and Applicative

data Error err a = Ok a | Failed err deriving Show

-- The idea is to accumulater errors that occures during computation
instance Monoid err => Applicative (Error err) where
  pure = Ok

  Ok f <*> Ok v = Ok $ f v
  Ok _ <*> Failed err = Failed err
  Failed err <*> Ok _ = Failed err
  Failed err1 <*> Failed err2 = Failed $ err1 <> err2

-- for example consider that we have list of urls
urls = ["redit.com", "err1", "vk.com", "err2"]

download :: String -> Error [String] String
download "err1" = Failed ["Not existing domain"]
download "err2" = Failed ["Not existing domain - 2"]
download _      = Ok "Some usefull data"

-- now launch: traverse download urls
