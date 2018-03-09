{-# LANGUAGE KindSignatures #-}

{-
  Code from:
  https://www.schoolofhaskell.com/user/bartosz/understanding-algebras

  Cool article to understand F-Algebras
  what is it
  why to use
  and how it works!
-}

module UnderstandingFAlgebras where

import           Data.Char

-- simple recursive expression
data Expr' = Const' Int
  | Add' Expr' Expr'
  | Mul' Expr' Expr'

-- could be defined without recursion
data ExprF a = Const Int
  | Add a a
  | Mul a a

{- We can apply ExprF to itselve infinitely many times
  ExprF (ExprF (ExprF (... (ExprF a)))...)
  After infinitely many iterations we should get to a fix point
  where further iterations make no difference.
  It means that applying one more ExprF would't change anything -- a fix point doesn't move under ExprF.
  It's like adding one to infinity: you get back infinity.
-}

-- fix point of a type constructor f
-- In the literature you'll sometimes see Fix called Mu.

-- We only need one generic recursive type, Fix,
-- to be able to crank out other recursive types from (non-recursive) type constructors.

-- Fx :: f (Fix f) -> Fix f
newtype Fix (f :: * -> *) = Fx (f (Fix f))

-- redefine Expr' using Fix
type Expr = Fix ExprF

-- we can always construct a value of Expr
-- because we have type constructor: Const Int (does not depends on 'a')
exampleExp :: Expr -- Fix ExprF
exampleExp = Fx $ (Fx $ Const 1) `Add` (Fx $ Const 2)

-- To evaluate Expr we need eval it reqursively
-- F-alegbra is built on top of a Functor
instance Functor ExprF where
  fmap eval (Const i) = Const i
  fmap eval (Add l r) = eval l `Add` eval r
  fmap eval (Mul l r) = eval l `Mul` eval r

-- Int is a carrier type of an algebra
alg :: ExprF Int -> Int
alg (Const i)   = i
alg (x `Add` y) = x + y
alg (x `Mul` y) = x * y

alg' :: ExprF String -> String
alg' (Const i)   = [chr (ord 'a' + i)]
alg' (x `Add` y) = x ++ y
alg' (x `Mul` y) = concat [[a, b] | a <- x, b <- y]

{-
  F-Algebras constists of:
  1. endofunctor F of category C
  2. an object A of that category
  3. morphism F(A) to A

  So for haskell:
  1. Functor f
  2. carrier type a
  3. f a -> a
-}

type Algebra f a = f a -> a

-- example
type ExampleAlgebra = Algebra ExprF Int

exAlg :: ExampleAlgebra
exAlg (Const i)   = i
exAlg (x `Add` y) = x + y
exAlg (x `Mul` y) = x * y

-- there are many algebras based on a given functor, but there is one initial
type InitialExprFAlgebra = Algebra ExprF (Fix ExprF)

-- ExprF (Expr) -> Expr
exInitAlg :: ExprF (Fix ExprF) -> Fix ExprF
exInitAlg = Fx

{-
  exInitAlg preserves all the information, oposing to other algebras
  that resuces expression. So exInitAlg is as poverfull as other algebras.

  Being initial it has unique homomorphism to other algebras
-}

-- we can peek into our expression
unFix :: Fix f -> f (Fix f)
unFix (Fx x) = x

-- this function generates evaluator for a given algebra
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix

eval :: Expr -> Int
eval = cata alg
-- now we can: eval exampleExp

-- Lists algebra
data ListF a b = Nil | Cons a b

instance Functor (ListF a) where
  fmap _ Nil        = Nil
  fmap f (Cons a b) = Cons a (f b)

algSum :: ListF Int Int -> Int
algSum Nil          = 0
algSum (Cons e acc) = e + acc

lst :: Fix (ListF Int)
lst = Fx $ Cons 2 (Fx $ Cons 3 (Fx $ Cons 4 (Fx Nil)))
-- cata algSum lst

-- So it is some generalisation of foldr


{-
  This code is taken from:
  http://web.cecs.pdx.edu/~sheard/course/AdvancedFP/notes/CoAlgebras/Code.html

  Good to follow up after that article to understand CoAlgebras
-}


data F1 x = Zero | One | Plus x x

-- for a given seed produce 'f newSeed'
type CoAlgebra f c = c -> f c

countdown :: CoAlgebra (ListF Int) Int
countdown 0 = Nil
countdown n = Cons n (n - 1)

data StreamF n x = C n x

endsIn0s :: CoAlgebra (StreamF Integer) [Integer]
endsIn0s []     = C 0 []
endsIn0s (x:xs) = C x xs

split :: CoAlgebra F1 Integer
split 0 = Zero
split 1 = One
split n = Plus (n-1) (n-2)

fibs :: CoAlgebra (StreamF Int) (Int,Int)
fibs (x, y) = C (x + y) (y, x + y)

instance Functor (StreamF n) where
  fmap f (C x y) = C x (f y)

instance Functor F1 where
  fmap _ Zero       = Zero
  fmap _ One        = One
  fmap f (Plus x y) = Plus (f x) (f y)


-- newtype Fix (f :: * -> *) = Fx (f (Fix f))
finalCoalg :: CoAlgebra a (Fix a)
finalCoalg = unFix

f1 :: Fix (ListF a)
f1 = Fx Nil

ones :: Fix (StreamF Integer)
ones = Fx (C 1 ones)

nats :: Fix (StreamF Integer)
nats = g 0 where g n = Fx (C n (g (n+1)))

data NatF x = Z | S x

omega :: Fix NatF
omega = f undefined
  where f x = Fx(S(f x))

n :: Int -> Fix NatF
n x = f x
  where f 0 = Fx Z
        f n = Fx(S (f (n-1)))

-- definition seems like
-- cata alg = alg . fmap (cata alg) . unFix
ana :: Functor f => CoAlgebra f seed -> seed -> Fix f
ana phi = Fx . fmap (ana phi) . phi

final1 = ana endsIn0s
final2 = ana split
final3 = ana fibs

tak :: (Num a, Eq a) => a -> Fix (StreamF b) -> [b]
tak 0 _             = []
tak n (Fx (C x xs)) = x : tak (n-1) xs
-- tak 5 (final3 (1,1))
-- tak 5 (final1 [1, 2, 3])
