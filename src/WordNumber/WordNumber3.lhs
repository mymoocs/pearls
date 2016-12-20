[[meta title="Word numbers, Part 3: Binary search"]]
[[meta author="Dylan Thurston"]]
[[meta authorurl="http://www.math.columbia.edu/~dpt/"]]
[[tag english]]

We return to [ITA Software](http://www.itasoftware.com/)'s "word
numbers" problem, continuing our work in [[part_1|WordNumbers1]] and
[[part_2|WordNumbers2]].  As before, you can download [this post as a program](https://conway.rutgers.edu/cgi-bin/viewvc.cgi/wiki/blog/posts/WordNumbers3.lhs?view=co).

>     {-# OPTIONS -W -fglasgow-exts #-}
>     module WordNumbers3 where
>     import WordNumbers1
>     import WordNumbers2
>
>     import Prelude hiding ((+), (*), sum, product)
>     import qualified Prelude as P
>     import Data.List (genericSplitAt, genericLength)

We left off in part 2 with a program that could quickly compute the
total number of characters produced in any grammar.  We will use that
program in this part to locate exactly where in the production the
*n*th letter is, in order to solve the following slightly easier
version of the puzzle:

 >  If the integers from 1 to 999,999,999 are written as words in
 >  order and concatenated, what is the 51 billionth letter?

(The alphabetical sorting was dropped.)  This version has appeared in
some of ITA Software's ads.

We solve this one by keeping track a binary tree corresponding to the
productions in the grammar, computing the total length of each
production and doing a search in this tree.

>     data Binary m = Binary m (Maybe (Binary m, Binary m))

Characters create leaf nodes---

>     instance (Character m) => Character (Binary m) where
>         char c = Binary (char c) Nothing

---and addition (i.e., alternate possibilities in the grammar) creates
a branch.

>     instance (Monoid m) => Monoid (Binary m) where
>         zero = Binary zero Nothing
>         b1@(Binary m1 _) + b2@(Binary m2 _) = Binary (m1 + m2) (Just (b1, b2))

Note that the addition operation is not commutative.  This is
impossible in a ring: in any ring the addition is necessarily
commutative.  (Exercise!)  But this does not hold in general for a
semiring (with no subtraction) or, more severely, for a semiring or
seminearring (which only has one of the two distributive laws).  This
is fortunate for us, since we want to be sure to keep the productions
in order.

The multiplication operation is a little more subtle, since we
multiply two trees, either of which may branch.  We use left-to-right
evaluation, taking by preference the branches of the left tree.

>     instance (Seminearring m) => Seminearring (Binary m) where
>         one = Binary one Nothing
>         b1@(Binary m1 c1) * b2@(Binary m2 c2)
>             = Binary (m1 * m2)
>                      (case c1 of
>                       Just (b11,b12) -> Just (b11*b2, b12*b2)
>                       Nothing -> case c2 of
>                                  Nothing -> Nothing
>                                  Just (b21,b22) -> Just (b1*b21, b1*b22))

Since in English the most significant digits are always on the left,
the resulting order of the leaves of the tree constructed for `ten9`
will be the usual numerical order.  If we were working in a language
where the least significant digits were stated first, we would need
right-to-left evaluation, or we could go to a more general solution
like the one we will later give for alphabetical sorting.

We will use these trees to keep track of the count and volume of the
productions (as in part 2), as well as the list of strings (so that we
can see what letter we get).

>     type Measure = ([String], Deriv Count Volume)

We treat the pair component-wise.

>     instance (Monoid a, Monoid b) => Monoid (a,b) where
>         zero = (zero, zero)
>         (a1,b1) + (a2,b2) = (a1+a2, b1+b2)

>     instance (Seminearring a, Seminearring b) => Seminearring (a,b) where
>         one = (one, one)
>         (a1,b1) * (a2,b2) = (a1*a2, b1*b2)

>     instance (Character r1, Character r2) => Character (r1, r2) where
>         char c = (char c, char c)

The binary search is now straightforward to write.

>     volume :: Deriv Count Volume -> Integer
>     volume (Deriv _ (Wrap (Nat v))) = v

>     search :: Binary Measure -> Integer -> Measure
>     search (Binary m Nothing) _ = m
>     search (Binary _ (Just (c1@(Binary (_,skip) _), c2))) i
>         | i' < 0    = search c1 i
>         | otherwise = let (s,m) = search c2 i' in (s, skip + m)
>         where i' = i - volume skip

For the answer, we return the target letter as well as its context.

>     answer n = (before, it, after)
>       where
>         target = pred n
>         ([string], d) = search ten9 target
>         end = volume d
>         (before, it:after) = genericSplitAt local string
>         local = genericLength string - (end - target)

We can now quickly solve the problem...

 >     *WordNumbers3> answer 51000000000
 >     ("sevenhundredthirtytwomil",'l',"ionsevenhundredninetysixthousandthreehundredsixtysix")

...and check a few small values to be sure there are no off by one errors.

 >     *WordNumbers3> answer 3
 >     ("on",'e',"")
 >     *WordNumbers3> answer 4
 >     ("",'t',"wo")
