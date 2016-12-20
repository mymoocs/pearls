{--
  Created       : 2016 Dec 07 (Wed) 02:08:34 PM by Arthur Vardanyan.
  Last Modified : 2016 Dec 07 (Wed) 02:08:41 PM by Arthur Vardanyan.
--}


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module WordNumber.WordNumber1 where

import Prelude hiding ((+), (*), sum, product, Monoid)
import qualified Prelude as P

infixl 6 +
class Monoid a where
  zero :: a
  (+) :: a -> a -> a



infixl 7 *
class (Monoid a) => Seminearring a where
  one :: a
  (*) :: a -> a -> a -- (x+y) * z = x*z + y*z on one side only.

instance Monoid [a] where
  zero = []
  (+) = (++)


-- |
--
-- >>> (["twenty"] + ["thirty"]) * ["","one","two"]
-- ["twenty","twentyone","twentytwo","thirty","thirtyone","thirtytwo"]
-- >>> ["twenty"] * ["","one","two"] + ["thirty"] * ["","one","two"]
-- ["twenty","twentyone","twentytwo","thirty","thirtyone","thirtytwo"]

instance Seminearring [[a]] where
  one = [[]]
  xss * yss = [ xs ++ ys | xs <- xss, ys <- yss ]

-- |
--
-- The seminearring [String] is generated by characters: every character maps to
-- an element of this seminearring. Let us represent this property by a type class.
class Character a where
  char :: Char -> a

instance Character Char where
  char = id

instance (Character a) => Character [a] where
  char c = [char c]

-- mapping from characters to strings by concatenating (multiplying) its output.
product :: (Seminearring a) => [a] -> a
product = foldr (*) one

--
string :: (Seminearring a, Character a) => String -> a
string = product . map char


sum :: (Monoid a) => [a] -> a
sum = foldr (+) zero

strings :: (Seminearring a, Character a) => String -> a
strings = sum . map string . words


-- }
-- type (Seminearring a, Character a) => a; that is, a value of any type where
-- we know how to add, multiply, and what to do with characters.
--
-- >>> length (ten6 :: [String])
-- 999999
-- >>> head (ten6 :: [String])
-- "one"
-- >>> last (ten6 :: [String])
-- "ninehundredninetyninethousandninehundredninetynine"
-- >>> length (concat (ten6 :: [String]))
-- 44872000
-- >>> take 5 (ten9 :: [String])
-- ["one","two","three","four","five"]




ten1, ten2, ten3, ten6, ten9 :: (Seminearring a, Character a) => a
ten1 = strings "one two three four five six seven eight nine"
ten2 = ten1
     + strings "ten eleven twelve"
     + (strings "thir four" + prefixes) * string "teen"
     + (strings "twen thir for" + prefixes) * string "ty" * (one + ten1)
    where prefixes = strings "fif six seven eigh nine"
ten3 = ten2 + ten1 * string "hundred" * (one + ten2)
ten6 = ten3 + ten3 * string "thousand" * (one + ten3)
ten9 = ten6 + ten3 * string "million" * (one + ten6)
