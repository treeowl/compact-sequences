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

module Data.CompactSequence.Stack.Topped
  ( Stack (Empty, (:<))
  , empty
  , cons
  , (<|)
  , uncons
--  , compareLength
--  , take
  , fromList
--  , fromListN
  ) where

import qualified Data.CompactSequence.Stack.Topped.Internal as S
import Data.CompactSequence.Stack.Topped.Internal hiding (Empty)
import Prelude hiding (take)

infixr 5 :<

-- | A bidirectional pattern synonym for working with
-- the front of a stack.
pattern (:<) :: a -> Stack a -> Stack a
pattern x :< xs <- (uncons -> Just (x, xs))
  where
    (:<) = cons

-- | A bidirectional pattern synonym for the empty stack.
pattern Empty :: Stack a
pattern Empty = S.Empty

{-# COMPLETE (:<), Empty #-}
