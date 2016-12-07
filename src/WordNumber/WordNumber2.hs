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


class (Seminearring r, Monoid m) => Module r m where
    (*>) :: r -> m -> m
    (*>) = flip (<*)
    (<*) :: m -> r -> m
    (<*) = flip (*>)
