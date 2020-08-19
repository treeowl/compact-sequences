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

module Data.CompactSequence.Queue.Simple.Internal
  ( Queue (.., Empty, (:<))
  , (|>)
  , empty
  , snoc
  , uncons
  , take
  , fromList
  , fromListN
  , fromListNIncremental
  ) where

import qualified Data.CompactSequence.Queue.Internal as Q
import qualified Data.CompactSequence.Internal.Array as A
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts
import Control.Monad.State.Strict
import qualified Control.Monad.State.Lazy as LS
import qualified Prelude as P
import Prelude hiding (take)

-- | A queue.
newtype Queue a = Queue (Q.Queue 'A.Mul1 a)
  deriving (Functor, Traversable, Eq, Ord)

-- | The empty queue.
empty :: Queue a
empty = Queue Q.empty

-- | Enqueue an element at the rear of a queue.
snoc :: Queue a -> a -> Queue a
snoc (Queue q) a = Queue $ Q.snocA A.one q (A.singleton a)

-- | An infix synonym for 'snoc'.
(|>) :: Queue a -> a -> Queue a
(|>) = snoc

-- | Dequeue an element from the front of a queue.
uncons :: Queue a -> Maybe (a, Queue a)
uncons (Queue q) = case Q.viewA A.one q of
  Q.EmptyA -> Nothing
  Q.ConsA sa q'
    | (# a #) <- A.getSingleton# sa
    -> Just (a, Queue q')

infixr 5 :<
infixl 4 `snoc`, |>

-- | A unidirectional pattern synonym for viewing the
-- front of a queue.
pattern (:<) :: a -> Queue a -> Queue a
pattern x :< xs <- (uncons -> Just (x, xs))

-- | A bidirectional pattern synonym for the empty queue.
pattern Empty :: Queue a
pattern Empty = Queue Q.Empty
{-# COMPLETE (:<), Empty #-}

instance Foldable Queue where
  -- TODO: Implement more methods?
  foldMap f (Queue q) = foldMap f q
  foldr c n (Queue q) = foldr c n q
  foldr' c n (Queue q) = F.foldr' c n q
  foldl f b (Queue q) = foldl f b q
  foldl' f b (Queue q) = F.foldl' f b q

  null (Queue Q.Empty) = True
  null _ = False
  -- Note: length only does O(log n) *unshared* work, but it does O(n) amortized
  -- work because it has to force the entire spine. We could avoid
  -- this, of course, by storing the size with the queue.
  length (Queue q) = go 0 A.one q
    where
      go :: Int -> A.Size m -> Q.Queue m a -> Int
      go !acc !_s Q.Empty = acc
      go !acc !s (Q.Node pr m sf) = go (acc + lpr + lsf) (A.twice s) m
        where
          lpr = case pr of
                  Q.FD1{} -> A.getSize s
                  Q.FD2{} -> 2*A.getSize s
                  Q.FD3{} -> 3*A.getSize s
          lsf = case sf of
                  Q.RD0 -> 0
                  Q.RD1{} -> A.getSize s
                  Q.RD2{} -> 2*A.getSize s

instance Show a => Show (Queue a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

instance Exts.IsList (Queue a) where
  type Item (Queue a) = a
  toList = F.toList
  fromList = fromList
  fromListN = fromListN

instance Semigroup (Queue a) where
  -- This gives us O(m + n) append. Can we do better?
  -- I suspect O(min(m,n)) might be possible.
  Empty <> q = q
  q <> Empty = q
  q <> r = fromListN (length q + length r) (F.toList q ++ F.toList r)

instance Monoid (Queue a) where
  mempty = empty

-- | Take up to the given number of elements from the front
-- of a queue to form a new queue. \( O(\min (k, n)) \), where
-- \( k \) is the integer argument and \( n \) is the size of
-- the queue.
take :: Int -> Queue a -> Queue a
take n s
  | n <= 0 = Empty
  | compareLength n s == LT
  = fromListN n (P.take n (F.toList s))
  | otherwise = s

-- | \( O(\min(m, n)) \). Compare an 'Int' to the length of a 'Queue'.
--
-- @compareLength n xs = compare n (length xs)@
compareLength :: Int -> Queue a -> Ordering
compareLength n0 (Queue que0) = go A.one n0 que0
  where
    go :: A.Size n -> Int -> Q.Queue n a -> Ordering
    go !_sz n Q.Empty = compare n 0
    go _sz n _ | n <= 0 = LT
    go sz n (Q.Node pr m sf)
      = go (A.twice sz) (n - frontLen sz pr - rearLen sz sf) m

frontLen :: A.Size n -> Q.FD n a -> Int
frontLen s Q.FD1{} = A.getSize s
frontLen s Q.FD2{} = 2 * A.getSize s
frontLen s Q.FD3{} = 3 * A.getSize s

rearLen :: A.Size n -> Q.RD n a -> Int
rearLen s Q.RD0{} = 0
rearLen s Q.RD1{} = A.getSize s
rearLen s Q.RD2{} = 2 * A.getSize s

-- | \( O(n \log n) \). Convert a list to a 'Queue', with the head of the
-- list at the front of the queue.
fromList :: [a] -> Queue a
fromList = F.foldl' snoc empty

-- | \( O(n) \). Convert a list of the given size to a 'Queue', with the
-- head of the list at the front of the queue.
fromListN :: Int -> [a] -> Queue a
fromListN n xs
  = Queue $ evalState (fromListQN A.one (N.toBin23 n)) xs

-- | \( O(n) \). Convert a list of the given size to a 'Queue', with the
-- head of the list at the front of the queue. Unlike 'fromListN',
-- the conversion is performed incrementally. This is generally
-- beneficial if the list is represented compactly (e.g., an enumeration)
-- or when it's otherwise not important to consume the entire list
-- immediately.
fromListNIncremental :: Int -> [a] -> Queue a
fromListNIncremental n xs
  = Queue $ LS.evalState (fromListQN A.one (N.toBin23 n)) xs

-- We use a similar approach to the one we use for stacks.  Every node of the
-- resulting queue will be safe, except possibly the last one. This should make
-- the resulting queue cheap to work with initially. In particular, each front
-- digit (except possibly the last) will be 2 or 3, and each rear digit will be
-- 0. This arrangement also lets us offer an incremental version of fromListN.

-- Without these SPECIALIZE pragmas, this doesn't get specialized
-- for some reason. Bleh!
{-# SPECIALIZE
  fromListQN :: A.Size n -> N.Bin23 -> State [a] (Q.Queue n a)
 #-}
{-# SPECIALIZE
  fromListQN :: A.Size n -> N.Bin23 -> LS.State [a] (Q.Queue n a)
 #-}
fromListQN :: MonadState [a] m => A.Size n -> N.Bin23 -> m (Q.Queue n a)
fromListQN !_ N.End23 = do
  remains <- get
  if null remains
    then pure Q.empty
    else error "Data.CompactSequence.Queue.Simple.fromListQN: List too long"
fromListQN !sz N.OneEnd23 = do
  sa <- state (A.arraySplitListN sz)
  remains <- get
  if null remains
    then pure $! Q.Node (Q.FD1 sa) Q.Empty Q.RD0
    else error "Data.CompactSequence.Queue.Simple.fromListQN: List too long"
fromListQN !sz (N.Two23 mn) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  m <- fromListQN (A.twice sz) mn
  pure $! Q.Node (Q.FD2 sa1 sa2) m Q.RD0
fromListQN !sz (N.Three23 mn) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  sa3 <- state (A.arraySplitListN sz)
  m <- fromListQN (A.twice sz) mn
  pure $! Q.Node (Q.FD3 sa1 sa2 sa3) m Q.RD0
