{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
{-# language LambdaCase #-}
{-# language BangPatterns #-}
module Main (main) where

import Data.Foldable
import Test.QuickCheck
import Test.QuickCheck.Poly
import Test.Tasty
import Test.Tasty.QuickCheck

import Data.CompactSequence.Queue.Simple.Internal
import qualified Data.CompactSequence.Queue.Simple.Internal as Q
import qualified Data.CompactSequence.Queue.Internal as QI
import qualified Data.CompactSequence.Internal.Array.Safe as A
import Prelude as P

instance Arbitrary a => Arbitrary (Queue a) where
  -- Generate stacks whose size is at most on the same order
  -- of magnitude as the size parameter, with any shape.
  arbitrary = sized $ \sz0 -> do
    sz <- choose (0, sz0)
    Queue <$> go A.one sz
    where
      go :: A.Size n -> Int -> Gen (QI.Queue n a)
      go !_ars n
        | n <= 0 = pure QI.Empty
      go !ars n = do
        frontSize <- choose (1,3 :: Int)
        rearSize <- choose (0,2 :: Int)
        m <- go (A.twice ars) (n - (frontSize + rearSize) * A.getSize ars)
        QI.Node <$> pr ars frontSize <*> pure m <*> sf ars rearSize

      pr !ars = \case
        1 -> QI.FD1 <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
        2 -> QI.FD2 <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
        _ -> QI.FD3 <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)

      sf !ars = \case
        0 -> pure QI.RD0
        1 -> QI.RD1 <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
        _ -> QI.RD2 <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)

  -- We shrink by trimming the spine. Any other shrinks will
  -- be tricky.
  shrink (Queue que) = [ Queue (takeSpine k que) | k <- [0..depth que]]
    where
      depth :: QI.Queue n a -> Int
      depth QI.Empty = 0
      depth (QI.Node _ m _) = 1 + depth m

      takeSpine :: Int -> QI.Queue n a -> QI.Queue n a
      takeSpine 0 !_ = QI.Empty
      takeSpine _ QI.Empty
        = QI.Empty
      takeSpine n (QI.Node pr m sf)
        = QI.Node pr (takeSpine (n - 1) m) sf

prop_identityA :: [A] -> Property
prop_identityA lst = toList (fromList lst) === lst

prop_identityB :: Queue A -> Property
prop_identityB stk = fromList (toList stk) === stk

prop_identityC :: [A] -> Property
prop_identityC lst = toList (fromListN (length lst) lst) === lst

prop_identityD :: Queue A -> Property
prop_identityD stk = fromListN (length stk) (toList stk) === stk

prop_identityE :: [A] -> Property
prop_identityE lst = toList (fromListNIncremental (length lst) lst) === lst

prop_snoc :: Queue A -> A -> Property
prop_snoc xs x = toList (xs |> x) === toList xs ++ [x]

prop_uncons :: Queue A -> Property
prop_uncons xs = case xs of
  Empty -> toList xs === []
  y :< ys -> toList xs === y : toList ys

prop_uncons_of_empty :: Property
prop_uncons_of_empty = uncons (Empty @(Queue A)) === Nothing

prop_append :: Queue A -> Queue A -> Property
prop_append xs ys = toList (xs <> ys) === toList xs ++ toList ys

--prop_compareLength :: Int -> Queue () -> Property
--prop_compareLength n s = compareLength n s === compare n (length s)

prop_take :: Int -> Queue A -> Property
prop_take n s = toList (Q.take n s) === P.take n (toList s)

return [] -- This makes sure the above properties are seen by $allProperties

all_props :: TestTree
all_props = testProperties "properties" $allProperties

main :: IO ()
main = defaultMain all_props
