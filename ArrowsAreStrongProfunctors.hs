{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}

{-
  This code is taken from:
  https://www.youtube.com/watch?v=hrNfkP8iKAs&list=WL&index=12&t=644s
  This talk introduces some categorical defenitions
  Than Profunctor is defined as well as composition of them,
  after that it is shown how using Yonedas lemma
  it is possible to prove that (->) is the left and the right unit of Profunctors composition

  Having that, we can define a category, where:
  objects: Profunctors
  morphisms: Natural transformations
  tensor product: Composition
  unit: (->)

  after that Arrows are introduced and it is shown that Arrows are Strong Profunctors
-}

module ArrowsAreStrongProfunctors where

import           Control.Monad ((>=>))
import qualified GHC.Base      (id, (.))
import           Prelude       hiding (Functor (..), Monoid (..), id, (.))

class Category cat where
  id :: a `cat` a
  (.) :: b `cat` c -> a `cat` b -> a `cat` c

instance Category (->) where
  id = GHC.Base.id
  (.) = (GHC.Base..)

class Monoid m where
  mu :: (m, m) -> m
  eta :: () -> m

newtype IntFun = IF (Int -> Int)

instance Monoid IntFun where
  mu (IF f, IF g) = IF (g . f)
  eta () = IF id

class Functor (f :: * -> *) where
  fmap :: (a -> b) -> (f a -> f b) -- lifts function a -> b, to f a -> f b

-- It is like functor but for product, dimap f g (el, el') => (f el, g el')
class Bifunctor (f :: * -> * -> *) where
  bimap :: (a -> a') -> (b -> b') -> f a b -> f a' b'

-- Contravariant in a and Covariant in b
class Profunctor (f :: * -> * -> *) where
  dimap :: (a' -> a) -> (b -> b') -> f a b -> f a' b'

instance Profunctor (->) where
  dimap :: (b -> a) -> (d -> c) -> (a -> d) -> (b -> c)
  dimap con pro f = pro . f . con

-- Inifinite product
type End p = forall x . p x x

newtype NatPro f g a b = NatPro (f a -> g b)

instance (Functor f, Functor g) => Profunctor (NatPro f g) where
  --                                    (f a -> g c)   (f b -> g d)
  dimap :: (b -> a) -> (c -> d) -> NatPro f g a c -> NatPro f g b d
  dimap ba cd (NatPro p) = NatPro $ fmap cd . p . fmap ba
  {-
    fa :: f b -> f a
    fa = fmap ba -- we take (f b) and do (f (ba b))

    gc :: f a -> g c
    gc = p

    gd :: g c -> g d
    gd = fmap cd

    -- In a nutshell very simmilar to instance Profunctor (->) where
    --   dimap con pro f = pro . f . con
    -- but:
    -- pro = gd
    -- f = gc
    -- con = fa
    res :: (f b -> g d)
    res = gd . gc . fa
  -}

-- Natural transformation,
-- It is like Functor for Functors, in functor we do:
-- f a -> f b
-- Natural transformation does:
-- f a -> g a
type Nat f g = End (NatPro f g)
-- type Nat f g = forall x . f x -> g x

-- inifinte Sum
data Coend p = forall x. Coend (p x x)

-- a -> b ~ a -> x -> b
data Compose p q a b = forall x. Compose (p a x) (q x b)
--                     exists x. (p a x, p x b)

instance (Profunctor p, Profunctor q) => Profunctor (Compose p q) where
  --                                (p a x, q x c) -> (p b x, q x d)
  dimap :: (b -> a) -> (c -> d) -> Compose p q a c -> Compose p q b d
  dimap ba cd (Compose pax qxc) = Compose (dimap ba id pax) (dimap id cd qxc)
  {-
    class Profunctor (p :: * -> * -> *) where
      dimap :: (b -> a) -> (c -> d) -> p a c -> p b d

    x is simmilar in both functions
    pax :: Profunctor p => a -> x -> p a x
    qxc :: Profunctor q => x -> c -> q x c

    for our instance we should implement
    dimap :: (b -> a) -> (c -> d) -> (p a x, q x c) -> (p b x, q x d)
    (p a x, q x c) is a pair of Profunctors

    so we have:
    (pax, qxc)
    ba :: (b -> a)
    cd :: (c -> d)

    We want:
    (p b x, q x d)

    We can do:
    left = dimap ba id pax -- so x is unchanged
    right = dimap id cd qxd -- so x is unchanged
    (left, right) :: (p b x, q x d)
  -}

-- data Compose p q a b = forall x. Compose (p a x) (q x b)
-- consider that we just remove x constraint
-- Or in other sense it is a BiFunctor: (a, y) -> (x , b)
data TensorProduct p q a b x y = TensorProduct (p a y) (q x b)

instance (Profunctor p, Profunctor q) => Profunctor (TensorProduct p q a b) where
  --    :: ex       ->  yd      -> (p a y, q x b)            -> (p a d, q e b)
  dimap :: (e -> x) -> (y -> d) -> TensorProduct p q a b x y -> TensorProduct p q a b e d
  dimap ex yd (TensorProduct pay qxb) = TensorProduct (dimap id yd pay) (dimap ex id qxb)

-- Now we can express Composition as Coend
type Compose' p q a b = Coend (TensorProduct p q a b)

-- pre Yoneda, not yet Yoneda but will become
newtype PreYoneda f a x y = PreYoneda ((a -> x) -> f y)

instance Functor f => Profunctor (PreYoneda f a) where
  --       dx       -> ye       -> ((a -> x) -> f y) -> ((a -> d) -> f e)
  dimap :: (d -> x) -> (y -> e) -> PreYoneda f a x y -> PreYoneda f a d e
  --                                          (a -> d)
  dimap dx ye (PreYoneda ax_fy) = PreYoneda $ \ad -> fmap ye (ax_fy (dx . ad))

newtype Yoneda f a = Yoneda (forall x. (a -> x) -> f x)
type Yoneda' f a = End (PreYoneda f a)

-- Yoneda lemma: Yoneda f a ~ f a, where f is a Functor
fromY :: Functor f => Yoneda f a -> f a
fromY (Yoneda axfx) = axfx id

toY :: Functor f => f a -> Yoneda f a
toY fa = Yoneda $ \ax -> fmap ax fa

data CoYoneda f a = forall x. CoYoneda (x -> a) (f x)

fromCY :: Functor f => CoYoneda f a -> f a
fromCY (CoYoneda xa fx) = fmap xa fx

toCY :: Functor f => f a -> CoYoneda f a
toCY fa = CoYoneda id fa

{-

  data Compose p q a b = forall x. Compose (p a x) (q x b)

  (->) is a right unit of composition
  Compose p (->) a b ~
  exists x. (p a x, x -> b) ~
  exists x. (x -> b, p a x) ~
  CoYoneda (p a) b ~
  p a b

  (->) is a left unit of composition
  Compose (->) p a b ~
  forall c. (Compose (->) p a b -> c) ~
  forall c. (exists x. (a -> x), p x b) -> c ~
  forall c x. (a -> x) -> (p x b -> c) ~
  forall c. Yoneda (p _ b -> c) a ~
  forall c. p a b -> c =>
  compose (->) p a b ~ p a b

  so Compose is a TensorProduct for the category of endofunctors, where morphsims are natural transformations
  and (->) is a unit
-}

class Profunctor p => Strong p where
  first' :: p a b -> p (a, x) (b, x)

-- Arrow is a monoid in the category of strong profunctors
class Category ar => Arrow (ar :: * -> * -> *) where
  arr :: (a -> b) -> ar a b
  first :: ar a b -> ar (a, x) (b, x)

infix 1 >>>
(>>>) :: Arrow ar => ar a b -> ar b c -> ar a c
a >>> a' = a' . a

newtype Kleisli m a b = Kl (a -> m b)

instance Monad m => Category (Kleisli m) where
  id = arr id
  (Kl f) . (Kl g) = Kl (g >=> f)

instance Monad m => Arrow (Kleisli m) where
  arr f = Kl $ return . f
  -- (a -> m b) -> (a, x) -> m (b, x)
  first (Kl f) = Kl $ \(a, x) -> do y <- f a; return (y, x)

