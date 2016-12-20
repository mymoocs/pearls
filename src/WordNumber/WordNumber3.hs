{--
  Created       : 2016 Dec 08 (Thu) 07:03:05 PM by Arthur Vardanyan.
  Last Modified : 2016 Dec 08 (Thu) 07:07:37 PM by Arthur Vardanyan.
--}

module WordNumber.WordNumber3 where
import WordNumber.WordNumber1
import WordNumber.WordNumber2

import Prelude hiding ((+), (*), sum, product, Monoid)
import qualified Prelude as P
import Data.List (genericSplitAt, genericLength)


data Binary m = Binary m (Maybe (Binary m, Binary m))

-- Characters create leaf nodes—
instance (Character m) => Character (Binary m) where
    char c = Binary (char c) Nothing

-- and addition (i.e., alternate possibilities in the grammar) creates a branch.
instance (Monoid m) => Monoid (Binary m) where
    zero = Binary zero Nothing
    b1@(Binary m1 _) + b2@(Binary m2 _) = Binary (m1 + m2) (Just (b1, b2))

-- Note that the addition operation is not commutative. This is impossible in
-- a ring: in any ring the addition is necessarily commutative. (Exercise!)
-- But this does not hold in general for a semiring (with no subtraction) or,
-- more severely, for a semiring or seminearring (which only has one of the two
-- distributive laws). This is fortunate for us, since we want to be sure to
-- keep the productions in order.

-- The multiplication operation is a little more subtle, since we multiply
-- two trees, either of which may branch. We use left-to-right evaluation,
-- taking by preference the branches of the left tree.

instance (Seminearring m) => Seminearring (Binary m) where
    one = Binary one Nothing
    b1@(Binary m1 c1) * b2@(Binary m2 c2)
        = Binary (m1 * m2)
                 (case c1 of
                  Just (b11,b12) -> Just (b11*b2, b12*b2)
                  Nothing -> case c2 of
                             Nothing -> Nothing
                             Just (b21,b22) -> Just (b1*b21, b1*b22))
