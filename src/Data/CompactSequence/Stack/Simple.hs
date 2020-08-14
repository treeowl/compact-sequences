{-# language Safe #-}

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
  , compareLength
  , take
  , fromList
  , fromListN
  ) where

import Data.CompactSequence.Stack.Simple.Internal
import Prelude ()
