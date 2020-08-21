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

import Data.CompactSequence.Deque.Simple.Internal
import qualified Data.CompactSequence.Deque.Simple.Internal as D
import qualified Data.CompactSequence.Deque.Internal as DI
import qualified Data.CompactSequence.Internal.Array.Safe as A
import qualified Data.CompactSequence.Internal.Size as Sz
import Prelude as P

instance Arbitrary a => Arbitrary (Deque a) where
  -- Generate stacks whose size is at most on the same order
  -- of magnitude as the size parameter, with any shape.
  arbitrary = sized $ \sz0 -> do
    sz <- choose (0, sz0)
    Deque <$> go Sz.one sz
    where
      go :: Sz.Size n -> Int -> Gen (DI.Deque n a)
      go !ars n
        | n <= 0 = pure DI.Empty
        | n <= Sz.getSize ars = DI.Shallow <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
      go !ars n = do
        frontSize <- choose (1,4 :: Int)
        rearSize <- choose (1,4 :: Int)
        m <- go (Sz.twice ars) (n - (frontSize + rearSize) * Sz.getSize ars)
        DI.Deep <$> dig ars frontSize <*> pure m <*> dig ars rearSize

      dig !ars = \case
        1 -> DI.One <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
        2 -> DI.Two <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
        3 -> DI.Three <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
        _ -> DI.Four <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)

{-
  -- We shrink by trimming the spine. Any other shrinks will
  -- be tricky.
  shrink (Deque que) = [ Deque (takeSpine k que) | k <- [0..depth que]]
    where
      depth :: DI.Deque n a -> Int
      depth DI.Empty = 0
      depth (DI.Node _ m _) = 1 + depth m

      takeSpine :: Int -> DI.Deque n a -> DI.Deque n a
      takeSpine 0 !_ = DI.Empty
      takeSpine _ DI.Empty
        = DI.Empty
      takeSpine n (DI.Node pr m sf)
        = DI.Node pr (takeSpine (n - 1) m) sf
-}

prop_identityA :: [A] -> Property
prop_identityA lst = toList (fromList lst) === lst

prop_identityB :: Deque A -> Property
prop_identityB stk = fromList (toList stk) === stk

prop_identityC :: [A] -> Property
prop_identityC lst = toList (fromListN (length lst) lst) === lst

prop_identityD :: Deque A -> Property
prop_identityD stk = fromListN (length stk) (toList stk) === stk

prop_snoc :: Deque A -> A -> Property
prop_snoc xs x = toList (xs |> x) === toList xs ++ [x]

prop_uncons :: Deque A -> Property
prop_uncons xs = case xs of
  Empty -> toList xs === []
  y :< ys -> toList xs === y : toList ys

prop_uncons_of_empty :: Property
prop_uncons_of_empty = uncons (Empty @(Deque A)) === Nothing

prop_append :: Deque A -> Deque A -> Property
prop_append xs ys = toList (xs <> ys) === toList xs ++ toList ys

--prop_compareLength :: Int -> Deque () -> Property
--prop_compareLength n s = compareLength n s === compare n (length s)

--prop_take :: Int -> Deque A -> Property
--prop_take n s = toList (D.take n s) === P.take n (toList s)

return [] -- This makes sure the above properties are seen by $allProperties

all_props :: TestTree
all_props = testProperties "properties" $allProperties

main :: IO ()
main = defaultMain all_props
