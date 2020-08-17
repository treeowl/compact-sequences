{-# language DeriveTraversable #-}
{-# language ScopedTypeVariables #-}
{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language DataKinds #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language Trustworthy #-}
{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{- OPTIONS_GHC -Wall #-}
{- OPTIONS_GHC -ddump-simpl #-}

{- |
Space-efficient queues with amortized \( O(\log n) \) operations.  These
directly use an underlying array-based implementation, without doing any
special optimization for the first few and last few elements of the queue.
-}

module Data.CompactSequence.Deque.Simple.Internal
  ( Deque (.., Empty, (:<), (:>))
  , (|>)
  , (<|)
  , empty
  , cons
  , snoc
  , uncons
  , unsnoc
--  , take
  , fromList
  , fromListN
  , fromListNIncremental
  ) where

import qualified Data.CompactSequence.Deque.Internal as D
import qualified Data.CompactSequence.Internal.Array as A
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts
import Control.Monad.State.Strict
import qualified Control.Monad.State.Lazy as LS
import qualified Prelude as P
import Prelude hiding (take)

-- | A queue.
newtype Deque a = Deque (D.Deque 'A.Mul1 a)
  deriving (Functor, Traversable, Eq, Ord)

-- | The empty queue.
empty :: Deque a
empty = Deque D.empty

-- | Enqueue an element at the front of a deque.
cons :: a -> Deque a -> Deque a
cons a (Deque q) = Deque $ D.consA A.one (A.singleton a) q

-- | Enqueue an element at the rear of a deque.
snoc :: Deque a -> a -> Deque a
snoc (Deque q) a = Deque $ D.snocA A.one q (A.singleton a)

-- | An infix synonym for 'snoc'.
(|>) :: Deque a -> a -> Deque a
(|>) = snoc

-- | An infix synonym for 'cons'.
(<|) :: a -> Deque a -> Deque a
(<|) = cons

-- | Dequeue an element from the front of a deque.
uncons :: Deque a -> Maybe (a, Deque a)
uncons (Deque q) = case D.viewLA A.one q of
  D.EmptyL -> Nothing
  D.ConsL sa q'
    | (# a #) <- A.getSingleton# sa
    -> Just (a, Deque q')

-- | Dequeue an element from the rear of a deque.
unsnoc :: Deque a -> Maybe (Deque a, a)
unsnoc (Deque q) = case D.viewRA A.one q of
  D.EmptyR -> Nothing
  D.SnocR q' ta
    | (# a #) <- A.getSingleton# ta
    -> Just (Deque q', a)

infixr 4 :<
infixl 4 `snoc`, |>

-- | A bidirectional pattern synonym for manipulating the
-- front of a deque.
pattern (:<) :: a -> Deque a -> Deque a
pattern x :< xs <- (uncons -> Just (x, xs))

-- | A bidirectional pattern synonym for manipulating the
-- rear of a deque.
pattern (:>) :: Deque a -> a -> Deque a
pattern xs :> x <- (unsnoc -> Just (xs, x))

-- | A bidirectional pattern synonym for the empty deque.
pattern Empty :: Deque a
pattern Empty = Deque D.Empty
{-# COMPLETE (:<), Empty #-}
{-# COMPLETE (:>), Empty #-}

instance Foldable Deque where
  -- TODO: Implement more methods?
  foldMap f (Deque q) = foldMap f q
  foldr c n (Deque q) = foldr c n q
  foldr' c n (Deque q) = F.foldr' c n q
  foldl f b (Deque q) = foldl f b q
  foldl' f b (Deque q) = F.foldl' f b q

  null (Deque D.Empty) = True
  null _ = False
{-
  -- Note: length only does O(log n) *unshared* work, but it does O(n) amortized
  -- work because it has to force the entire spine. We could avoid
  -- this, of course, by storing the size with the queue.
  length (Deque q) = go 0 A.one q
    where
      go :: Int -> A.Size m -> D.Deque m a -> Int
      go !acc !_s D.Empty = acc
      go !acc !s (D.Node pr m sf) = go (acc + lpr + lsf) (A.twice s) m
        where
          lpr = case pr of
                  D.FD1{} -> A.getSize s
                  D.FD2{} -> 2*A.getSize s
                  D.FD3{} -> 3*A.getSize s
          lsf = case sf of
                  D.RD0 -> 0
                  D.RD1{} -> A.getSize s
                  D.RD2{} -> 2*A.getSize s
-}

instance Show a => Show (Deque a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

{-
instance Exts.IsList (Deque a) where
  type Item (Deque a) = a
  toList = F.toList
  fromList = fromList
  fromListN = fromListN

instance Semigroup (Deque a) where
  -- This gives us O(m + n) append. Can we do better?
  -- I suspect O(min(m,n)) might be possible.
  Empty <> q = q
  q <> Empty = q
  q <> r = fromListN (length q + length r) (F.toList q ++ F.toList r)

instance Monoid (Deque a) where
  mempty = empty
-}

{-
-- | Take up to the given number of elements from the front
-- of a queue to form a new queue. \( O(\min (k, n)) \), where
-- \( k \) is the integer argument and \( n \) is the size of
-- the queue.
take :: Int -> Deque a -> Deque a
take n s
  | n <= 0 = Empty
  | compareLength n s == LT
  = fromListN n (P.take n (F.toList s))
  | otherwise = s

-- | \( O(\min(m, n)) \). Compare an 'Int' to the length of a 'Deque'.
--
-- @compareLength n xs = compare n (length xs)@
compareLength :: Int -> Deque a -> Ordering
compareLength n0 (Deque que0) = go A.one n0 que0
  where
    go :: A.Size n -> Int -> D.Deque n a -> Ordering
    go !_sz n D.Empty = compare n 0
    go _sz n _ | n <= 0 = LT
    go sz n (D.Node pr m sf)
      = go (A.twice sz) (n - frontLen sz pr - rearLen sz sf) m

frontLen :: A.Size n -> D.FD n a -> Int
frontLen s D.FD1{} = A.getSize s
frontLen s D.FD2{} = 2 * A.getSize s
frontLen s D.FD3{} = 3 * A.getSize s

rearLen :: A.Size n -> D.RD n a -> Int
rearLen s D.RD0{} = 0
rearLen s D.RD1{} = A.getSize s
rearLen s D.RD2{} = 2 * A.getSize s
-}

-- | \( O(n \log n) \). Convert a list to a 'Deque', with the head of the
-- list at the front of the queue.
fromList :: [a] -> Deque a
fromList = F.foldl' snoc empty

-- | \( O(n) \). Convert a list of the given size to a 'Deque', with the
-- head of the list at the front of the queue.
fromListN :: Int -> [a] -> Deque a
fromListN n xs
  = fromList xs
--  = Deque $ evalState (fromListQN A.one (N.toBin23 n)) xs

-- | \( O(n) \). Convert a list of the given size to a 'Deque', with the
-- head of the list at the front of the queue. Unlike 'fromListN',
-- the conversion is performed incrementally. This is generally
-- beneficial if the list is represented compactly (e.g., an enumeration)
-- or when it's otherwise not important to consume the entire list
-- immediately.
fromListNIncremental :: Int -> [a] -> Deque a
fromListNIncremental n xs
  = fromList xs
{-
  = Deque $ LS.evalState (fromListQN A.one (N.toBin23 n)) xs

-- We use a similar approach to the one we use for stacks.  Every node of the
-- resulting queue will be safe, except possibly the last one. This should make
-- the resulting queue cheap to work with initially. In particular, each front
-- digit (except possibly the last) will be 2 or 3, and each rear digit will be
-- 0. This arrangement also lets us offer an incremental version of fromListN.

-- Without these SPECIALIZE pragmas, this doesn't get specialized
-- for some reason. Bleh!
{-# SPECIALIZE
  fromListQN :: A.Size n -> N.Bin23 -> State [a] (D.Deque n a)
 #-}
{-# SPECIALIZE
  fromListQN :: A.Size n -> N.Bin23 -> LS.State [a] (D.Deque n a)
 #-}
fromListQN :: MonadState [a] m => A.Size n -> N.Bin23 -> m (D.Deque n a)
fromListQN !_ N.End23 = do
  remains <- get
  if null remains
    then pure D.empty
    else error "Data.CompactSequence.Deque.Simple.fromListQN: List too long"
fromListQN !sz N.OneEnd23 = do
  sa <- state (A.arraySplitListN sz)
  remains <- get
  if null remains
    then pure $! D.Node (D.FD1 sa) D.Empty D.RD0
    else error "Data.CompactSequence.Deque.Simple.fromListQN: List too long"
fromListQN !sz (N.Two23 mn) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  m <- fromListQN (A.twice sz) mn
  pure $! D.Node (D.FD2 sa1 sa2) m D.RD0
fromListQN !sz (N.Three23 mn) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  sa3 <- state (A.arraySplitListN sz)
  m <- fromListQN (A.twice sz) mn
  pure $! D.Node (D.FD3 sa1 sa2 sa3) m D.RD0
-}
