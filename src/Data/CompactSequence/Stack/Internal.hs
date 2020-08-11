{-# language BangPatterns, DeriveTraversable #-}
{-# language TypeFamilies #-}
{-# language DataKinds #-}
{-# language TypeOperators #-}
{-# language NoStarIsType #-}
{-# language Safe #-}
{-# language ScopedTypeVariables #-}
{-# language InstanceSigs #-}
module Data.CompactSequence.Stack.Internal where
import qualified Data.Foldable as F
import qualified Data.CompactSequence.Internal.Array.Safe as A
import Data.CompactSequence.Internal.Array.Safe (Array, Size)
import Data.Function (on)
import Data.Traversable (foldMapDefault)
import Prelude

data Stack n a
  = Empty
  | One !(Array n a) !(Stack ('A.Twice n) a)
  | Two !(Array n a) !(Array n a) (Stack ('A.Twice n) a)
  | Three !(Array n a) !(Array n a) !(Array n a) !(Stack ('A.Twice n) a)
  deriving (Functor, Traversable)
{-
Debit invariant: We allow the Stack in each Two node as many debits as there
are elements in its array and those of all previous Two nodes.

We derive Functor and Traversable, at least for now, even though the derived
fmap and traverse can produce extra thunks below Two nodes. For Functor, there
seems to be no possible advantage to being stricter, except possibly to get
more consistent performance with different stack shapes--all we could do would
be to push the thunks to the leaves, which is really always worse. I suspect
the same is true for traverse, but I'm not entirely sure.
-}

instance Eq a => Eq (Stack n a) where
  (==) = (==) `on` F.toList

instance Ord a => Ord (Stack n a) where
  compare = compare `on` F.toList

instance Show a => Show (Stack n a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

instance Foldable (Stack n) where
  foldMap f xs = foldMapDefault f xs

  foldr :: forall a b. (a -> b -> b) -> b -> Stack n a -> b
  foldr c n = go
    where
      go :: Stack m a -> b
      go Empty = n
      go (One sa more)
        = foldr c (go more) sa
      go (Two sa1 sa2 more)
        = foldr c (foldr c (go more) sa2) sa1
      go (Three sa1 sa2 sa3 more)
        = foldr c (foldr c (foldr c (go more) sa3) sa2) sa1
  {-# INLINE foldr #-}

  null Empty = True
  null _ = False

  -- TODO: Once the size representation is properly sorted,
  -- we should implement a custom length method.

  -- length does O(log n) *unshared* work, but since
  -- it forces the spine it does O(n) *amortized* work.
  -- The right way to get stack sizes efficiently is to track
  -- them separately.
  length = go 1 0
    where
      go :: Int -> Int -> Stack m a -> Int
      go !_s acc Empty = acc
      go s acc (One _ more) = go (2*s) (acc + s) more
      go s acc (Two _ _ more) = go (2*s) (acc + 2*s) more
      go s acc (Three _ _ _ more) = go (2*s) (acc + 3*s) more

empty :: Stack n a
empty = Empty

consA :: Size n -> Array n a -> Stack n a -> Stack n a
consA !_ sa Empty = One sa Empty
consA !_ sa1 (One sa2 more) = Two sa1 sa2 more
consA !_ sa1 (Two sa2 sa3 more) = Three sa1 sa2 sa3 more
consA n sa1 (Three sa2 sa3 sa4 more) = Two sa1 sa2 (consA (A.twice n) (A.append n sa3 sa4) more)

{-
Empty is always trivial.

One: We increase the debit allowance below.

Two: We reduce the debit allowance of some nodes below by 2. We pay 2*log n to
discharge the excess debits.

Three: This is the tricky case for `cons`. We have some number of Three
nodes followed by something else. For each `Three` node, we suspend `s/4`
array-doubling work. We pay for that using the additional debit allowance
we gain from the elements in the new `Two` node. When we reach the end
of the `Three` chain, we have either `Empty`, `One`, or `Two`. If we have
`Empty` or `One`, we're done. If we have `Two`, then changing that to
`Three` reduces the debit allowance below. But we also *gain* debit allowance
below, from all the `Three`s that have changed to `Two`s! Our net loss
debit allowance is just 1, so we're golden.

1 2 4
Three Three Two more
-> Two Two Three more
`more` starts with a debit allowance of 8. The Three node in the
result has a debit allowance of 6. We suspend 3/2 array-doubling
work total and pass the debits from the `Stack` in the last `Two`
up to the one in the first `Two`.

Three Three Three Two more
-> Two Two Two Three more
`more` starts witha  debit allowance of 16. The Three node in the
result has a debit allowance of 14. We suspend 7/2 array doubling
work. Of that, 1/2 is in the first Two, 2/2 is in the second Two,
and 4/2 is in the last Two; we pass the debits on the last up, to
get 2/2 in the first Two and 4/2 in the second.

Three Three Three Three Two more
-> Two Two Two Two Three more
We suspend 15/2 array doubling work:
1    2    4    0
1/2, 2/2, 4/2, 8/2
1/2     1     2

Three Three Three Three Three Two more
We suspend 31/2 array doubling work:
1    2    4    8    0
1/2, 2/2, 4/2, 8/2, 16/2
1/2, 2/2, 4/2, 8/2


Three Three One more
-> Two Two Two more

-}

data ViewA n a = EmptyA | ConsA !(Array n a) (Stack n a)

unconsA :: Size n -> Stack n a -> ViewA n a
unconsA !_ Empty = EmptyA
unconsA !_ (Three sa1 sa2 sa3 more) = ConsA sa1 (Two sa2 sa3 more)
unconsA !_ (Two sa1 sa2 more) = ConsA sa1 (One sa2 more)
unconsA n (One sa more) = ConsA sa $
  case unconsA (A.twice n) more of
    EmptyA -> Empty
    ConsA sa1 more' -> Two sa2 sa3 more'
      where
        (sa2, sa3) = A.splitArray n sa1

{-
Cases:
Empty is trivial.
`Three`: we increase the debit allowance below.
`Two`: We reduce the debit allowance on certain nodes by 2; pay 2*log n to discharge that.
`One`: This is the hard case. We have some number of `One` nodes followed by something else.
For each `One`, we perform a split. We place debits to pay for those, discharging the ones
at the root. At the end, we have a situation similar to that for `cons`: the tricky case
is ending in `Two`, where we use the fact that all the new `Two`s pay for the loss of the
final `Two`.


One One One Two
-}
