{--
  Created       : 2016 Dec 07 (Wed) 02:08:34 PM by Arthur Vardanyan.
  Last Modified : 2016 Dec 21 (Wed) 03:03:53 PM by Arthur Vardanyan.
--}


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module WordNumber.DigitNumber1 where

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


skip :: Int -> [a] -> [a]
skip 0 xs = xs
skip _ [] = []
skip n (x:xs) = skip (n-1) xs

-- tem2' - two digits numbers [10..99]
-- ten2  - [1..99]
-- ten3' - [100..999]
-- ten3  - [1..999]
ten1, ten1', ten2, ten2', ten3, ten3', ten4', ten4,
      ten5, ten5', ten6, ten6',
      ten7, ten7', ten8, ten8', ten9, ten9' :: (Seminearring a, Character a) => a
ten1' = strings "0 1 2 3 4 5 6 7 8 9"
ten1  = strings   "1 2 3 4 5 6 7 8 9"
ten2' = ten1  * ten1'
ten2  = ten1  + ten2'
ten3' = ten2' * ten1'
ten3  = ten2  + ten3'
ten4' = ten3' * ten1'
ten4  = ten3  + ten4'
ten5' = ten4' * ten1'
ten5  = ten4  + ten5'
ten6' = ten5' * ten1'
ten6  = ten5  + ten6'
{--
ten6' = ten3 * (strings "00" * ten1' + strings "0" * ten2'  + ten3')
ten6  = ten4 + ten5'
ten6_1  = ten3 + ten3 * (strings "00" * ten1' + strings "0" * ten2'  + ten3')
--}
ten7' = ten6' * ten1'
ten7  = ten6  + ten7'
ten8' = ten7' * ten1'
ten8  = ten7  + ten8'
ten9' = ten8' * ten1'
ten9  = ten8  + ten9'

-- ten9  = ten6 + ten3' * (strings "000" * ten1' + strings "00" * ten2'
--                                   +  ten3' +  ten6')



testAt :: Int -> [String] -> Bool
testAt n xs = xs!!(n-1) == show n

test :: [String] -> Bool
test xs = and . map (\(a,b) -> a == show b) $ zip xs [1..]

test' :: [String] -> [(Bool, String, Integer)]
test' xs = map (\(a,b) -> (a == show b, a, b)) $ zip xs [1..]

test2  = test ten2
test3  = test ten3
test4  = test ten4
test5  = test ten5
test6  = test ten6
test7  = test ten7
test8  = test ten8
test9  = test ten9

-- take 10 $ filter (\(b, _, _) -> not b) test9'
test6' xs = test' ten6
test9' xs = test' ten9
