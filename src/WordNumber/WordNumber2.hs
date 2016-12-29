{-# LANGUAGE FlexibleInstances #-}
{--
  Created       : 2016 Dec 07 (Wed) 02:08:13 PM by Arthur Vardanyan.
  Last Modified : 2016 Dec 27 (Tue) 03:30:50 PM by Arthur Vardanyan.
--}
-- http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers2/



{-# LANGUAGE MultiParamTypeClasses #-}
module WordNumber.WordNumber2 where

import WordNumber.WordNumber1

import Prelude hiding ((+), (*), sum, product, Monoid, (*>), (<*))
import qualified Prelude as P


newtype Nat a = Nat a deriving (Eq, Ord)
type Count = Nat Integer

instance (Show a) => Show (Nat a) where
    show (Nat x) = show x

instance (Num a) => Monoid (Nat a) where
    zero = Nat 0
    Nat a + Nat b = Nat (a P.+ b)

instance (Num a) => Seminearring (Nat a) where
    one = Nat 1
    Nat a * Nat b = Nat (a P.* b)


-- |
-- >>> ten9 :: Count
-- 999999999
-- >>> map char "asdasd" :: [Count]
-- [1,1,1,1,1,1]
-- >>> product [Nat 1, Nat 10, Nat 12] :: Count
-- 120
instance (Num a) => Character (Nat a) where
    char _ = one



-- In general, the derivatives need to be a module over the scalars
-- (the base seminearring), with addition (a monoid structure),
-- and multiplication by scalars

-- (This structure is more properly called a bimodule, because we allow
-- multiplication by scalars on both sides.)

class (Seminearring r, Monoid m) => Module r m where
    (*>) :: r -> m -> m
    (*>) = flip (<*) -- (x * y) *> m = x * (y *> m)
    (<*) :: m -> r -> m
    (<*) = flip (*>) -- m <* (x * y) = (m <* x) * y


-- distributive law
-- (x *> m) <* y = x *> (m <* y)

-- Now a derivative as a pair of a value and a derivative
-- http://www.danielbrice.net/blog/10/
-- So, you’d think of the Deriv 4 0.5 as saying the function’s value is 4 right now,
-- and its derivative is 0.5 right now.
data Deriv r m = Deriv r m deriving (Eq, Show)


-- satisfying the usual law for addition d(f+g) = df + dg
instance (Monoid r, Monoid m) => Monoid (Deriv r m) where
    zero = Deriv zero zero
    Deriv c1 m1 + Deriv c2 m2 = Deriv (c1 + c2) (m1 + m2)


-- while for multiplication we use Leibniz’s rule, d(f·g) = f·dg + df·g.
-- for instance, the total length of the strings from one to nine is used a
-- total of nine times, but we don’t want to count their length that many times.
-- Instead we count how many times they will be used, and multiply using Leibniz’s rule.
instance (Module r m) => Seminearring (Deriv r m) where
    one = Deriv one zero
    Deriv c1 m1 * Deriv c2 m2 = Deriv (c1 * c2) (c1 *> m2 + m1 <* c2)


-- We convert characters to derivatives component-wise.
instance (Character r, Character m) => Character (Deriv r m) where
    char c = Deriv (char c) (char c)


-- To actually use these derivatives, we introduce a wrapper type to keep track
-- of the units, with some obvious instances.

newtype Wrap s a = Wrap a deriving (Eq, Ord)

instance (Monoid a) => Monoid (Wrap s a) where
    zero = Wrap zero
    Wrap a + Wrap b = Wrap (a + b)

instance (Show a) => Show (Wrap s a) where
    show (Wrap x) = show x

instance (Seminearring a) => Seminearring (Wrap s a) where
    one = Wrap one
    Wrap a * Wrap b = Wrap (a * b)

instance (Seminearring r) => Module r (Wrap s r) where
    r *> Wrap m = Wrap (r * m)
    Wrap m <* r = Wrap (m * r)


-- In our case, the units are numbers of characters, which we call Volume.
data V
type Volume = Wrap V (Nat Integer)


-- | Every character has length one:
--
-- >>> ten9 :: Deriv Count Volume
-- Deriv 999999999 70305000000
-- >>> ten6 :: Deriv Count Volume
-- Deriv 999999 44872000
-- >>> ten2 :: Deriv Count Volume
-- Deriv 99 854
instance Character Volume where
    char _ = one
