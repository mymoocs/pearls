[[meta title="Word numbers, Part 2"]]
[[meta author="Dylan Thurston"]]
[[meta authorurl="http://www.math.columbia.edu/~dpt/"]]
[[tag english]]

We return to [ITA Software](http://www.itasoftware.com/)'s "word
numbers" problem, like the following:

 >  If the integers from 1 to 999,999,999 are written as words, sorted
 >  alphabetically, and concatenated, what is the 51 billionth letter?

In the [[first_part|WordNumbers1]], we came up with a problem
statement.  We defined a term `ten9` of type `(Seminearring a,
Character a) => a`; that is, a value of any type where we know how to
add, multiply, and what to do with characters.  For instance, `ten9`
could take a values in `[String]`:

 >     *WordNumbers1> take 5 (ten9 :: [String])
 >     ["one","two","three","four","five"]

and the answer to the above problem is easy to write:

 >     *WordNumbers1> concat (List.sort (ten9 :: [String])) !! 51000000000
 >     *** Exception: Prelude.(!!): negative index

As you can see, though, this specification has no chance of working:
the indexing function `(!!)` takes an `Int` as its second argument,
which one my computer cannot represent numbers bigger than
2<sup>31</sup>, which is only around 2 billion.  This limitation
merely represents a practical limitation, that you are unlikely to be
able to work with lists that are so colossally big, and indeed the
computation above would take much too long to complete.

In this post we will start to solve such problems efficiently.  We
start by counting the total length of all strings in `ten9`.  The key
idea is to think of converting lists of strings to polynomials, where
each character gets mapped to the variable <i>x</i>, a string of
length <i>n</i> gets mapped to <i>x<sup>n</sup></i>, and a list of
strings get mapped to a sum.  Thus instead of a list starting

 >     ["one","two","three","four","five",...]

we get a polynomial whose first few terms are

 > <i>x</i><sup>3</sup> + <i>x</i><sup>3</sup> + <i>x</i><sup>5</sup> + <i>x</i><sup>4</sup> + <i>x</i><sup>4</sup> + ...

If we evaluate this polynomial at <i>x</i> = 1, we get the total
number of terms, which is not very interesting.  If we instead take
the derivative first, we get

 > 3<i>x</i><sup>2</sup> + 3<i>x</i><sup>2</sup> + 5<i>x</i><sup>4</sup> + 4<i>x</i><sup>3</sup> + 4<i>x</i><sup>3</sup> + ...

Now evaluation at <i>x</i> = 1 gives

 > 3 + 3 + 5 + 4 + 4 + ...

which is the total length of all these strings, as desired.

To implement this efficiently, we use the idea of *automatic
differentiation*: we can make the value and first derivative of a
function around <i>x</i> = 1 into a seminearring supporting addition
and multiplication.  (We could include subtraction and division if we
wanted, but we do not need it here.)  Conceptually, it is best to
think about this as the first two terms in the Taylor series
expansion, as we will explain more below.

We now turn to the implementation.  As before, you can download [this post as a program](https://conway.rutgers.edu/cgi-bin/viewvc.cgi/wiki/blog/posts/WordNumbers2.lhs?view=co).
First we import what we did previously.

>     {-# OPTIONS -W -fglasgow-exts #-}
>     module WordNumbers2 where
>     import WordNumbers1
>
>     import Prelude hiding ((+), (*), sum, product)
>     import qualified Prelude as P

As a warm-up, we first count the total number of strings, using the
fact that natural numbers are a nearring.

>     newtype Nat a = Nat a deriving (Eq, Ord)
>     type Count = Nat Integer

>     instance (Show a) => Show (Nat a) where
>         show (Nat x) = show x

>     instance (Num a) => Monoid (Nat a) where
>         zero = Nat 0
>         Nat a + Nat b = Nat (a P.+ b)

>     instance (Num a) => Seminearring (Nat a) where
>         one = Nat 1
>         Nat a * Nat b = Nat (a P.* b)

We convert every character into the number 1. This corresponds to the
evaluation at <i>x</i> = 1 as explained above.

>     instance (Num a) => Character (Nat a) where
>         char _ = one

We check our work by counting the total number of terminals in the
grammar for `ten9`.

 >     *WordNumbers2> ten9 :: Count
 >     999999999

Note that we get 10<sup>9</sup> - 1 since 'zero' is not produced by
the grammar.

To compute the total count of all letters, we need a kind of
derivative, as mentioned above.  In general, we want to keep track of
the value of a function and its first derivative.  If we are working
with several variables (as we will later), the first derivative
becomes a vector of partial derivatives.  In general, the derivatives
need to be a *module* over the scalars (the base seminearring),
with addition (a monoid structure), and multiplication by scalars---

>     class (Seminearring r, Monoid m) => Module r m where
>         (*>) :: r -> m -> m
>         (*>) = flip (<*)
>         (<*) :: m -> r -> m
>         (<*) = flip (*>)

---satisfying associativities `(x*y) *> m = x * (y*>m)`,
`m <* (x*y) = (m<*x) * y`, and `(x*>m) <* y = x *> (m<*y)`
along with various distributive laws.
(It's not clear to me precisely which distributive laws should hold
for a general seminearring.)

(This structure is more properly called a *bimodule*, because
we allow multiplication by scalars on both sides.)

Now a derivative as a pair of a value and a derivative---

>     data Deriv r m = Deriv r m deriving (Eq, Show)

---satisfying the usual law for addition <i>d</i>(<i>f</i>+<i>g</i>) = <i>df</i> + <i>dg</i>---

>     instance (Monoid r, Monoid m) => Monoid (Deriv r m) where
>         zero = Deriv zero zero
>         Deriv c1 m1 + Deriv c2 m2 = Deriv (c1 + c2) (m1 + m2)

---while for multiplication we use Leibniz's rule, <i>d</i>(<i>f</i>&middot;<i>g</i>) = <i>f</i>&middot;<i>dg</i> + <i>df</i>&middot;<i>g</i>.

>     instance (Module r m) => Seminearring (Deriv r m) where
>         one = Deriv one zero
>         Deriv c1 m1 * Deriv c2 m2 = Deriv (c1 * c2) (c1 *> m2 + m1 <* c2)

We convert characters to derivatives component-wise.

>     instance (Character r, Character m) => Character (Deriv r m) where
>         char c = Deriv (char c) (char c)

To actually use these derivatives, we introduce a wrapper type to keep
track of the units, with some obvious instances.

>     newtype Wrap s a = Wrap a deriving (Eq, Ord)

>     instance (Monoid a) => Monoid (Wrap s a) where
>         zero = Wrap zero
>         Wrap a + Wrap b = Wrap (a + b)

>     instance (Show a) => Show (Wrap s a) where
>         show (Wrap x) = show x

>     instance (Seminearring a) => Seminearring (Wrap s a) where
>         one = Wrap one
>         Wrap a * Wrap b = Wrap (a * b)

>     instance (Seminearring r) => Module r (Wrap s r) where
>         r *> Wrap m = Wrap (r * m)
>         Wrap m <* r = Wrap (m * r)

In our case, the units are numbers of characters, which we call `Volume`.

>     data V

>     type Volume = Wrap V (Nat Integer)

Every character has length one:

>     instance Character Volume where char _ = one

We could change this definition to count, for instance, the total
number of pen strokes used to write all these letters.

Now we can quickly count the total number of characters in the English
words from one to a billion.

 >     *WordNumbers2> ten9 :: Deriv Count Volume
 >     Deriv 999999999 70305000000

For a sanity check, we check the count to a million...

 >     *WordNumbers2> ten6 :: Deriv Count Volume
 >     Deriv 999999 44872000

... which agrees with our previous result, but completes much more
quickly.

It's worth thinking about how this works. In computing

 >     *WordNumbers2> ten2 :: Deriv Count Volume
 >     Deriv 99 854

for instance, the total length of the strings from `one` to `nine` is
used a total of nine times, but we don't want to count their length
that many times.  Instead we count how many times they will be used,
and multiply using Leibniz's rule.

In the next installment we will use this setup to find the 51
billionth letter of this sequence (omitting the sorting), and then we
will move on to see how to sort the sequence while maintaining
efficiency.

**Update:** Added one associativity law that I forgot earlier.
