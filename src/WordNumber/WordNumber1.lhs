
[[meta title="Word numbers, Part 1: Billion approaches"]]
[[tag english]]

[ITA Software](http://www.itasoftware.com/) recruits computer scientists using
puzzles such as [the
following](http://www.itasoftware.com/careers/puzzles07.html).

 >  If the integers from 1 to 999,999,999 are written as words, sorted
 >  alphabetically, and concatenated, what is the 51 billionth letter?

In a series of posts, [Dylan Thurston](http://www.math.columbia.edu/~dpt/) and
I will solve this problem step by step, introducing concepts such as
[monoids](http://en.wikipedia.org/wiki/Monoid) and
[differentiation](http://en.wikipedia.org/wiki/Derivative) along the way.  We
will use the programming language [Haskell](http://www.haskell.org): every post
will be a [literate program](http://en.wikipedia.org/wiki/Literate_programming)
that you can run as is.  For example, you can download [this post as a program](https://conway.rutgers.edu/cgi-bin/viewvc.cgi/wiki/blog/posts/WordNumbers1.lhs?view=co).

Our basic strategy is quintessential computer science: first write a program to
specify the problem, then interpret the program creatively to find the solution
before the [the universe ends](http://en.wikipedia.org/wiki/Heat_death_of_the_universe).
Our first step, then, is to specify how to write integers as words in English.
Such a specification defines a long list of strings

 >     ["one", "two", ...,
 >      "onehundred", ...,
 >      "ninehundredninetyninemillionninehundredninetyninethousandninehundredninetynine"]

of type `[String]`.  There is a lot of repetitive structure within and among
these strings.  We need to express this structure concisely so that we can
exploit it later to solve the problem efficiently.

The structure we will use is that lists of strings form a *seminearring*.  To
use the nice-looking symbols `+` and `*` for operations in a seminearring, we
hide the definitions of these operators from the `Prelude`, but we will keep
the same infix precedences.

>     {-# LANGUAGE FlexibleInstances #-}
>     module WordNumbers1 where

>     import Prelude hiding ((+), (*), sum, product, Monoid)
>     import qualified Prelude as P

>     infixl 6 +
>     infixl 7 *

A seminearring is first of all a *monoid*.  A monoid is a set along with an
associative operation `+` and its identity element `zero`.

>     class Monoid a where
>       zero :: a
>       (+) :: a -> a -> a

(The `Data.Monoid` module already defines a `Monoid` type class, but our
notation fits better with the development below.)  Any list type is a monoid:
addition is concatenation, and the identity is the empty list.

>     instance Monoid [a] where
>       zero = []
>       (+) = (++)

You can think of `+` as [nondeterministic choice](http://www.informatik.uni-trier.de/~ley/db/conf/fpca/fpca85.html#Wadler85) and `zero` as failure.

A seminearring is a monoid with an additional associative operation `*` and its
identity element `one`---

>     class (Monoid a) => Seminearring a where
>       one :: a
>       (*) :: a -> a -> a

---satisfying distributivity `(x+y) * z = x*z + y*z` on *one side only*.
That is, the other distribution law `x * (y+z) = x*y + x*z` does not
necessarily hold (hence the "near" in "seminearring").  For example, every
list-of-list type (including `[String]` because `String` is just `[Char]`) is a
seminearring: to multiply two string lists is to concatenate every string in
the first list and every string in the second list; the identity for this
operation is the singleton list containing the empty string.

>     instance Seminearring [ [a] ] where
>       one = [[]]
>       xss * yss = [ xs ++ ys | xs <- xss, ys <- yss ]

Whereas distributivity holds on one side...

 >     *WordNumbers1> (["twenty"] + ["thirty"]) * ["","one","two"]
 >     ["twenty","twentyone","twentytwo","thirty","thirtyone","thirtytwo"]
 >     *WordNumbers1> ["twenty"] * ["","one","two"] + ["thirty"] * ["","one","two"]
 >     ["twenty","twentyone","twentytwo","thirty","thirtyone","thirtytwo"]

... it does not hold on the other side.

 >     *WordNumbers1> ["twenty","thirty"] * (["","one"] + ["two"])
 >     ["twenty","twentyone","twentytwo","thirty","thirtyone","thirtytwo"]
 >     *WordNumbers1> ["twenty","thirty"] * ["","one"] + ["twenty","thirty"] * ["two"]
 >     ["twenty","twentyone","thirty","thirtyone","twentytwo","thirtytwo"]

We require distributivity on one side only because a list of choices, unlike a
set of choices, is ordered: concatenating a choice of 2 strings and a choice of
3 strings yields a choice of 6 strings, but there are two obvious ways to order
the output choices, depending on which input choices are grouped together.  The
definition of `*` in the instance above enforces *left-to-right evaluation*:
the leftmost choice is the outermost loop.  This convention makes sense for
English because we pronounce the most significant digit first and we want a
list of English strings ordered by their numeric value.  Unfortunately,
[some mathematicians use the opposite convention](http://www.numdam.org/item?id=CM_1967__18_1-2_65_0).

The seminearring `[String]` is generated by characters: every
character maps to an element of this seminearring.  Let us represent this
property by a type class.

>     class Character a where
>       char :: Char -> a

>     instance Character Char where
>       char = id

>     instance (Character a) => Character [a] where
>       char c = [char c]

We can extend this mapping from characters to strings by concatenating
(multiplying) its output.

>     product :: (Seminearring a) => [a] -> a
>     product = foldr (*) one

>     string :: (Seminearring a, Character a) => String -> a
>     string = product . map char

We can now express a choice of strings, such as a digit between `"one"` and
`"three"`, not just as a list of strings but generically as a value of any type
that is an instance of `Seminearring` and `Character`.

 >     string "one" + string "two" + string "three" :: (Seminearring a, Character a) => a

We can specify a choice of words more concisely as a space-delimited string, as
in `strings "one two three"`.

>     sum :: (Monoid a) => [a] -> a
>     sum = foldr (+) zero

>     strings :: (Seminearring a, Character a) => String -> a
>     strings = sum . map string . words

We can now concisely define the list of 10<sup>9</sup>−1 strings at the core
of the ITA problem, in a way that expresses its repetitive structure.

>     ten1, ten2, ten3, ten6, ten9 :: (Seminearring a, Character a) => a
>     ten1 = strings "one two three four five six seven eight nine"
>     ten2 = ten1
>          + strings "ten eleven twelve"
>          + (strings "thir four" + prefixes) * string "teen"
>          + (strings "twen thir for" + prefixes) * string "ty" * (one + ten1)
>         where prefixes = strings "fif six seven eigh nine"
>     ten3 = ten2 + ten1 * string "hundred" * (one + ten2)
>     ten6 = ten3 + ten3 * string "thousand" * (one + ten3)
>     ten9 = ten6 + ten3 * string "million" * (one + ten6)

If you ignore the order of strings in these lists, the code above is just a
[[wikipedia context-free grammar]] for numbers in English.  It is a bit strange
for `one` to mean the empty string (usually notated ε or λ), but you get used
to it.  And it is super natural for `+` to mean alternation and `*` to mean
concatenation.

We can check by brute force that `ten6` contains 10<sup>6</sup>−1 strings,
but the same check on `ten9` exhausted my patience.

 >     *WordNumbers1> length (ten6 :: [String])
 >     999999
 >     *WordNumbers1> length (ten9 :: [String])
 >     Interrupted.

We can even compute the total length of all words between

 >     *WordNumbers1> head (ten6 :: [String])
 >     "one"

and

 >     *WordNumbers1> last (ten6 :: [String])
 >     "ninehundredninetyninethousandninehundredninetynine"

by evaluating

 >     *WordNumbers1> length (concat (ten6 :: [String]))
 >     44872000

by brute force.  But again, the same computation on `ten9` exhausted my
patience.

 >     *WordNumbers1> length (concat (ten9 :: [String]))
 >     Interrupted.


In the next post, we will compute the total length of `ten9` without trying my
patience.
