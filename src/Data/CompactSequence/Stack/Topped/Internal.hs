{-# language BangPatterns #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language TypeFamilies #-}
{-# language DeriveTraversable #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
-- We need Trustworthy for the IsList instance. *sigh*
{-# language Trustworthy #-}

{- |
Space-efficient stacks with amortized \( O(\log n) \) operations.
These directly use an underlying array-based implementation,
without doing any special optimization for the very top of the
stack.
-}

module Data.CompactSequence.Stack.Topped.Internal
  ( Stack (..)
  , empty
  , cons
  , (<|)
  , uncons
--  , compareLength
--  , take
  , fromList
--  , fromListN
  ) where

import qualified Data.CompactSequence.Stack.Internal as S
import Data.CompactSequence.Stack.Internal (consA, unconsA, ViewA (..))
import Data.CompactSequence.Internal.Size (Size, Twice)
import qualified Data.CompactSequence.Internal.Size as Sz
import Data.CompactSequence.Internal.Size (Sz4, sz4)
import qualified Data.CompactSequence.Internal.Array.Safe as A
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts
import qualified Prelude as P
import Data.Function (on)
import Prelude hiding (take)

-- | A stack.
data Stack a
  = One a !(S.Stack Sz4 a)
  | Two a a (S.Stack Sz4 a)
  | Three a a a (S.Stack Sz4 a)
  | Four a a  a a (S.Stack Sz4 a)
  | Five a a  a a a (S.Stack Sz4 a)
  | Six a a  a a a a (S.Stack Sz4 a)
  | Seven a a a  a a a a !(S.Stack Sz4 a)
  | Empty
  deriving (Functor, Foldable, Traversable)

instance Eq a => Eq (Stack a) where
  (==) = (==) `on` F.toList

instance Ord a => Ord (Stack a) where
  compare = compare `on` F.toList

-- | The empty stack.
empty :: Stack a
empty = Empty

infixr 5 `cons`, <|

-- | Push an element onto the front of a stack.
cons :: a -> Stack a -> Stack a
cons a Empty = One a S.Empty
cons a (One b m) = Two a b m
cons a (Two b c m) = Three a b c m
cons a (Three b c d m) = Four a b c d m
cons a (Four b c d e m) = Five a b c d e m
cons a (Five b c d e f m) = Six a b c d e f m
cons a (Six b c d e f g m) = Seven a b c d e f g m
cons a (Seven b c d e f g h m)
  = Four a b c d $ S.consA sz4 (A.mk4 e f g h) m

-- | Pop an element off the front of a stack.
uncons :: Stack a -> Maybe (a, Stack a)
uncons (Seven a b c d e f g  m)
  = Just (a, Six b c d e f g  m)
uncons (Six a b c d e f  m)
  = Just (a, Five b c d e f  m)
uncons (Five a b c d e  m)
  = Just (a, Four b c d e  m)
uncons (Four a b c d  m)
  = Just (a, Three b c d  m)
uncons (Three a b c  m)
  = Just (a, Two b c  m)
uncons (Two a b  m)
  = Just (a, One b  m)
uncons (One a  m)
  = Just (a, case S.unconsA Sz.sz4 m of
      ConsA ar m'
        | (# b, c, d, e #) <- A.get4# ar
        -> Four b c d e m'
      EmptyA -> Empty)
uncons Empty = Nothing


-- | An infix synonym for 'cons'.
(<|) :: a -> Stack a -> Stack a
(<|) = cons


instance Foldable Stack where
  -- TODO: implement more methods.
  foldMap f (Stack s) = foldMap f s
  foldr c n (Stack s) = foldr c n s
  foldl' f b (Stack s) = F.foldl' f b s
  null (Stack s) = null s

  -- length does O(log n) *unshared* work, but since
  -- it forces the spine it does O(n) *amortized* work.
  -- The right way to get stack sizes efficiently is to track
  -- them separately.
  length Empty = 0
  length (One _ m) = S.lengthWith Sz.sz 1 m
  length (Two _ _ m) = S.lengthWith Sz.sz 2 m
  length (Three _ _ _ m) = S.lengthWith Sz.sz 3 m
  length (Four _ _ _ _ m) = S.lengthWith Sz.sz 4 m
  length (Five _ _ _ _ _ m) = S.lengthWith Sz.sz 5 m
  length (Six _ _ _ _ _ _ m) = S.lengthWith Sz.sz 6 m
  length (Seven _ _ _ _ _ _ _ m) = S.lengthWith Sz.sz 7 m


{-

-- | \( O(\min(m, n)) \). Compare an 'Int' to the length of a 'Stack'.
--
-- @compareLength n xs = compare n (length xs)@
compareLength :: Int -> Stack a -> Ordering
compareLength n0 (Stack stk0) = go Sz.one n0 stk0
  where
    go :: Size n -> Int -> S.Stack n a -> Ordering
    go !_sz n S.Empty = compare n 0
    go _sz n _ | n <= 0 = LT
    go sz n (S.One _ more) = go (Sz.twice sz) (n - Sz.getSize sz) more
    go sz n (S.Two _ _ more) = go (Sz.twice sz) (n - 2*Sz.getSize sz) more
    go sz n (S.Three _ _ _ more) = go (Sz.twice sz) (n - 3*Sz.getSize sz) more

-- | Take up to the given number of elements from the front
-- of a stack to form a new stack. \( O(\min (k, n)) \), where
-- \( k \) is the integer argument and \( n \) is the size of
-- the stack.
take :: Int -> Stack a -> Stack a
take n s
  | n <= 0 = Empty
  | compareLength n s == LT
  = fromListN n (P.take n (F.toList s))
  | otherwise = s

-}

{-
instance Semigroup (Stack a) where
  -- This gives us O(m + n) append. I believe it's possible to
  -- achieve O(m). See #12 for a sketch.
  Empty <> s = s
  s <> Empty = s
  s <> t = fromListN (length s + length t) (F.toList s ++ F.toList t)

instance Monoid (Stack a) where
  mempty = empty
-}

instance Exts.IsList (Stack a) where
  type Item (Stack a) = a
  toList = F.toList
  fromList = fromList
--  fromListN = fromListN

-- | \( O(n \log n) \). Convert a list to a stack, with the
-- first element of the list as the top of the stack.
fromList :: [a] -> Stack a
fromList = foldr cons empty

{-

-- | \( O(n) \). Convert a list of known length to a stack,
-- with the first element of the list as the top of the stack.
fromListN :: Int -> [a] -> Stack a
fromListN n !_
  | n < 0 = error "Data.CompactSequence.Stack.fromListN: Negative argument."
fromListN s xs = Stack $ S.fromListSN Sz.one (N.toDyadic s) xs
-}

instance Show a => Show (Stack a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)
