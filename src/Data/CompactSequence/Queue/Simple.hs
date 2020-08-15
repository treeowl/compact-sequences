{-# language Safe #-}

{- |
Space-efficient queues with amortized \( O(\log n) \) operations.  These
directly use an underlying array-based implementation, without doing any
special optimization for the first few and last few elements of the queue.
-}

module Data.CompactSequence.Queue.Simple
  ( Queue (Empty, (:<))
  , (|>)
  , empty
  , snoc
  , uncons
  , take
  , fromList
  , fromListN
  ) where

import Data.CompactSequence.Queue.Simple.Internal
import Prelude hiding (take)
