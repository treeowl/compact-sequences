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

module Data.CompactSequence.Stack.Simple
  ( Stack (Empty, (:<))
  , empty
  , cons
  , (<|)
  , uncons
  , fromListN
  ) where

import qualified Data.CompactSequence.Stack.Internal as S
import Data.CompactSequence.Stack.Internal (consA, unconsA, ViewA (..))
import qualified Data.CompactSequence.Internal.Array.Safe as A
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts

newtype Stack a = Stack {unStack :: S.Stack A.Mul1 a}
  deriving (Functor, Traversable, Eq, Ord)
  -- TODO: Write a custom Traversable instance to avoid
  -- an extra fmap at the top.

empty :: Stack a
empty = Stack S.empty

infixr 4 `cons`, :<, <|
cons :: a -> Stack a -> Stack a
cons a (Stack s) = Stack $ consA A.one (A.singleton a) s

uncons :: Stack a -> Maybe (a, Stack a)
uncons (Stack stk) = do
  ConsA sa stk' <- pure $ unconsA A.one stk
  hd <- A.getSingletonA sa
  Just (hd, Stack stk')

(<|) :: a -> Stack a -> Stack a
(<|) = cons

pattern (:<) :: a -> Stack a -> Stack a
pattern x :< xs <- (uncons -> Just (x, xs))
  where
    (:<) = cons

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

instance Semigroup (Stack a) where
  -- This gives us O(m + n) append, which I believe is the best we can do in
  -- general.
  -- TODO: when the first stack is small enough, it's better to
  -- just push all its elements, in reverse, onto the second
  -- stack. Let's take advantage of that.
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
fromListN s xs = Stack $ fromListSN A.one (intToStackNum s) xs

-- We implement fromListN using a sort of abstract interpretation.  The
-- StackNum type is a representation of the *shape* of a stack.  Incrementing
-- it takes O(1) amortized time and O(log n) worst-case time. We count up with
-- it all the way to the desired size and then build a stack with the shape it
-- indicates. 
--
-- TODO: find a faster way. While this approach is much, much better than the
-- naive O(n log n) one, it's not great. The smallest improvement would be to
-- represent StackNum as a bitstring, with two bits per digit.  But it would be
-- much nicer to find a way to reduce the order of growth.

data StackNum
  = EmptyNum
  | OneNum !StackNum
  | TwoNum !StackNum
  | ThreeNum !StackNum

fromListSN :: A.Size n -> StackNum -> [a] -> S.Stack n a
fromListSN !_ EmptyNum xs
  | F.null xs = S.Empty
  | otherwise = error "Data.CompactSequence.Stack.fromListN: List too long."
fromListSN s (OneNum n') xs
  | (ar, xs') <- A.arraySplitListN s xs
  = S.One ar (fromListSN (A.twice s) n' xs')
fromListSN s (TwoNum n') xs
  | (ar1, xs') <- A.arraySplitListN s xs
  , (ar2, xs'') <- A.arraySplitListN s xs'
    -- We build eagerly to dispose of the list as soon as
    -- possible.
  = S.Two ar1 ar2 $! fromListSN (A.twice s) n' xs''
fromListSN s (ThreeNum n') xs
  | (ar1, xs') <- A.arraySplitListN s xs
  , (ar2, xs'') <- A.arraySplitListN s xs'
  , (ar3, xs''') <- A.arraySplitListN s xs''
  = S.Three ar1 ar2 ar3 (fromListSN (A.twice s) n' xs''')

intToStackNum :: Int -> StackNum
intToStackNum = go EmptyNum
  where
    go !sn 0 = sn
    go !sn n = go (incStackNum sn) (n - 1)

incStackNum :: StackNum -> StackNum
incStackNum EmptyNum = OneNum EmptyNum
incStackNum (OneNum n) = TwoNum n
incStackNum (TwoNum n) = ThreeNum n
incStackNum (ThreeNum n) = TwoNum (incStackNum n)

instance Show a => Show (Stack a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)
