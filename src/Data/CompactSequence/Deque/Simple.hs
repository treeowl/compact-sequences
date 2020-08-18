{-# language Safe #-}

{- |
Space-efficient queues with amortized \( O(\log n) \) operations.  These
directly use an underlying array-based implementation, without doing any
special optimization for the first few and last few elements of the queue.
-}

module Data.CompactSequence.Deque.Simple
  ( Deque (Empty, (:<), (:>))
  , (|>)
  , empty
  , cons
  , snoc
  , uncons
  , unsnoc
--  , take
  , fromList
  , fromListN
  ) where

import Data.CompactSequence.Deque.Simple.Internal
import Prelude ()
