{-# language DeriveTraversable #-}
{-# language ScopedTypeVariables #-}
{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language Trustworthy #-}
{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{- OPTIONS_GHC -Wall #-}
{- OPTIONS_GHC -ddump-simpl #-}

{- |
Space-efficient deques with amortized \( O(\log n) \) operations.  These
directly use an underlying array-based implementation, without doing any
special optimization for the first few and last few elements of the deque.
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
  ) where

import qualified Data.CompactSequence.Deque.Internal as D
import qualified Data.CompactSequence.Internal.Array as A
import qualified Data.CompactSequence.Internal.Size as Sz
import Data.CompactSequence.Internal.Size (Size)
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import qualified GHC.Exts as Exts
import Control.Monad.State.Strict
import qualified Prelude as P
import Prelude hiding (take)

-- | A deque.
newtype Deque a = Deque (D.Deque Sz.Sz1 a)
  deriving (Functor, Traversable, Eq, Ord)

-- | The empty deque.
empty :: Deque a
empty = Deque D.empty

-- | Enqueue an element at the front of a deque.
cons :: a -> Deque a -> Deque a
cons a (Deque q) = Deque $ D.consA Sz.one (A.singleton a) q

-- | Enqueue an element at the rear of a deque.
snoc :: Deque a -> a -> Deque a
snoc (Deque q) a = Deque $ D.snocA Sz.one q (A.singleton a)

-- | An infix synonym for 'snoc'.
(|>) :: Deque a -> a -> Deque a
(|>) = snoc

-- | An infix synonym for 'cons'.
(<|) :: a -> Deque a -> Deque a
(<|) = cons

-- | Dequeue an element from the front of a deque.
uncons :: Deque a -> Maybe (a, Deque a)
uncons (Deque q) = case D.viewLA Sz.one q of
  D.EmptyL -> Nothing
  D.ConsL sa q'
    | (# a #) <- A.getSingleton# sa
    -> Just (a, Deque q')

-- | Dequeue an element from the rear of a deque.
unsnoc :: Deque a -> Maybe (Deque a, a)
unsnoc (Deque q) = case D.viewRA Sz.one q of
  D.EmptyR -> Nothing
  D.SnocR q' ta
    | (# a #) <- A.getSingleton# ta
    -> Just (Deque q', a)

infixr 5 `cons`, :<, <|
infixl 4 `snoc`, :>, |>

-- | A bidirectional pattern synonym for manipulating the
-- front of a deque.
pattern (:<) :: a -> Deque a -> Deque a
pattern x :< xs <- (uncons -> Just (x, xs))
  where
    x :< xs = x `cons` xs

-- | A bidirectional pattern synonym for manipulating the
-- rear of a deque.
pattern (:>) :: Deque a -> a -> Deque a
pattern xs :> x <- (unsnoc -> Just (xs, x))
  where
    xs :> x = xs `snoc` x

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

  -- Note: length only does O(log n) *unshared* work, but it does O(n) amortized
  -- work because it has to force the entire spine. We could avoid
  -- this, of course, by storing the size with the dequeue.
  length (Deque q) = go 0 Sz.one q
    where
      go :: Int -> Size m -> D.Deque m a -> Int
      go !acc !_s D.Empty = acc
      go !acc !s (D.Shallow _) = acc + Sz.getSize s
      go !acc !s (D.Deep pr m sf) = go (acc + ld pr + ld sf) (Sz.twice s) m
        where
          ld = \case
                  D.One{} -> Sz.getSize s
                  D.Two{} -> 2*Sz.getSize s
                  D.Three{} -> 3*Sz.getSize s
                  D.Four{} -> 4*Sz.getSize s

instance Show a => Show (Deque a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

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

-- | \( O(n \log n) \). Convert a list to a 'Deque', with the head of the
-- list at the front of the deque.
fromList :: [a] -> Deque a
fromList = F.foldl' snoc empty

-- | \( O(n) \). Convert a list of the given size to a 'Deque', with the
-- head of the list at the front of the deque.
fromListN :: Int -> [a] -> Deque a
fromListN n xs
  = Deque $ evalState (D.fromListNM Sz.one n) xs
