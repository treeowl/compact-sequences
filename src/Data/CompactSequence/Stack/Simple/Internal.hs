{-# language DataKinds #-}
{-# language BangPatterns #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language TypeFamilies #-}
{-# language DeriveTraversable #-}
-- We need Trustworthy for the IsList instance. *sigh*
{-# language Trustworthy #-}

{- |
Space-efficient stacks with amortized \( O(\log n) \) operations.
These directly use an underlying array-based implementation,
without doing any special optimization for the very top of the
stack.
-}

module Data.CompactSequence.Stack.Simple.Internal
  ( Stack (.., Empty, (:<))
  , empty
  , cons
  , (<|)
  , uncons
  , compareLength
  , take
  , fromList
  , fromListN
  ) where

import qualified Data.CompactSequence.Stack.Internal as S
import Data.CompactSequence.Stack.Internal (consA, unconsA, ViewA (..))
import qualified Data.CompactSequence.Internal.Array.Safe as A
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts
import qualified Prelude as P
import Prelude hiding (take)

-- | A stack.
newtype Stack a = Stack {unStack :: S.Stack A.Mul1 a}
  deriving (Functor, Traversable, Eq, Ord)
  -- TODO: Write a custom Traversable instance to avoid
  -- an extra fmap at the top.

-- | The empty stack.
empty :: Stack a
empty = Stack S.empty

infixr 4 `cons`, :<, <|

-- | Push an element onto the front of a stack.
cons :: a -> Stack a -> Stack a
cons a (Stack s) = Stack $ consA A.one (A.singleton a) s

-- | Pop an element off the front of a stack.
uncons :: Stack a -> Maybe (a, Stack a)
uncons (Stack stk) = do
  ConsA sa stk' <- pure $ unconsA A.one stk
  hd <- A.getSingletonA sa
  Just (hd, Stack stk')

-- | An infix synonym for 'cons'.
(<|) :: a -> Stack a -> Stack a
(<|) = cons

-- | A bidirectional pattern synonym for working with
-- the front of a stack.
pattern (:<) :: a -> Stack a -> Stack a
pattern x :< xs <- (uncons -> Just (x, xs))
  where
    (:<) = cons

-- | A bidirectional pattern synonym for the empty stack.
pattern Empty :: Stack a
pattern Empty = Stack S.Empty

{-# COMPLETE (:<), Empty #-}

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
  length (Stack xs) = go 1 0 xs
    where
      go :: Int -> Int -> S.Stack m a -> Int
      go !_s acc S.Empty = acc
      go s acc (S.One _ more) = go (2*s) (acc + s) more
      go s acc (S.Two _ _ more) = go (2*s) (acc + 2*s) more
      go s acc (S.Three _ _ _ more) = go (2*s) (acc + 3*s) more

-- | \( O(\min(m, n)) \). Compare an 'Int' to the length of a 'Stack'.
--
-- @compareLength n xs = compare n (length xs)@
compareLength :: Int -> Stack a -> Ordering
compareLength n0 (Stack stk0) = go A.one n0 stk0
  where
    go :: A.Size n -> Int -> S.Stack n a -> Ordering
    go !_sz n S.Empty = compare n 0
    go _sz n _ | n <= 0 = LT
    go sz n (S.One _ more) = go (A.twice sz) (n - A.getSize sz) more
    go sz n (S.Two _ _ more) = go (A.twice sz) (n - 2*A.getSize sz) more
    go sz n (S.Three _ _ _ more) = go (A.twice sz) (n - 3*A.getSize sz) more

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

instance Semigroup (Stack a) where
  -- This gives us O(m + n) append. I believe it's possible to
  -- achieve O(m). See #12 for a sketch.
  Empty <> s = s
  s <> Empty = s
  s <> t = fromListN (length s + length t) (F.toList s ++ F.toList t)

instance Monoid (Stack a) where
  mempty = empty

instance Exts.IsList (Stack a) where
  type Item (Stack a) = a
  toList = F.toList
  fromList = fromList
  fromListN = fromListN

-- | \( O(n \log n) \). Convert a list to a stack, with the
-- first element of the list as the top of the stack.
fromList :: [a] -> Stack a
fromList = foldr cons empty

-- | \( O(n) \). Convert a list of known length to a stack,
-- with the first element of the list as the top of the stack.
fromListN :: Int -> [a] -> Stack a
fromListN n !_
  | n < 0 = error "Data.CompactSequence.Stack.fromListN: Negative argument."
fromListN s xs = Stack $ fromListSN A.one (N.toDyadic s) xs

-- We convert the size to a dyadic representation
-- (1-2 binary) and use that as the shape of the stack.
fromListSN :: A.Size n -> N.Dyadic -> [a] -> S.Stack n a
fromListSN !_ N.DEnd xs
  | F.null xs = S.Empty
  | otherwise = error "Data.CompactSequence.Stack.fromListN: List too long."
fromListSN s (N.DOne n') xs
  | (ar, xs') <- A.arraySplitListN s xs
  = S.One ar (fromListSN (A.twice s) n' xs')
fromListSN s (N.DTwo n') xs
  | (ar1, xs') <- A.arraySplitListN s xs
  , (ar2, xs'') <- A.arraySplitListN s xs'
    -- We build eagerly to dispose of the list as soon as
    -- possible.
  = S.Two ar1 ar2 $! fromListSN (A.twice s) n' xs''

instance Show a => Show (Stack a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)
