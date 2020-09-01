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

import Data.CompactSequence.Stack.Topped.Internal hiding (Empty)
import Data.CompactSequence.Stack.Topped (Stack (..))
import qualified Data.CompactSequence.Stack.Topped.Internal as S
import qualified Data.CompactSequence.Stack.Internal as SI
import qualified Data.CompactSequence.Internal.Array.Safe as A
import qualified Data.CompactSequence.Internal.Size as Sz
import Prelude as P

instance Arbitrary a => Arbitrary (Stack a) where
  -- Generate stacks whose size is at most on the same order
  -- of magnitude as the size parameter, with any shape.
  arbitrary = sized $ \sz0 -> do
    sz <- chooseInt (0, sz0)
    oneof . concat $
      [[pure Empty | sz == 0]
      ,[One <$> arbitrary <*> go Sz.sz4 (sz - 1) | sz >= 1]
      ,[Two <$> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 2) | sz >= 2]
      ,[Three <$> arbitrary <*> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 3) | sz >= 3]
      ,[Four <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 4) | sz >= 4]
      ,[Five <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 5) | sz >= 5]
      ,[Six <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 6) | sz >= 6]
      ,[Seven <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> go Sz.sz4 (sz - 7) | sz >= 7]]
    where
      go :: Sz.Size n -> Int -> Gen (SI.Stack n a)
      go !_ars n
        | n <= 0 = pure SI.Empty
      go !ars n = choose (1,3 :: Int) >>= \case
        1 -> SI.One <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> go (Sz.twice ars) (n - Sz.getSize ars)
        2 -> SI.Two <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                    <*> go (Sz.twice ars) (n - 2 * Sz.getSize ars)
        3 -> SI.Three <$> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                      <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                      <*> (A.fromList ars <$> vectorOf (Sz.getSize ars) arbitrary)
                      <*> go (Sz.twice ars) (n - 3 * Sz.getSize ars)
{-

  -- We shrink by trimming the spine. Any other shrinks will
  -- be tricky.
  shrink (Stack stk) = [ Stack (takeSpine k stk) | k <- [0..depth stk]]
    where
      depth :: SI.Stack n a -> Int
      depth SI.Empty = 0
      depth (SI.One _ m) = 1 + depth m
      depth (SI.Two _ _ m) = 1 + depth m
      depth (SI.Three _ _ _ m) = 1 + depth m

      takeSpine :: Int -> SI.Stack n a -> SI.Stack n a
      takeSpine 0 !_ = SI.Empty
      takeSpine _ SI.Empty
        = SI.Empty
      takeSpine n (SI.One sa1 m)
        = SI.One sa1 $ takeSpine (n - 1) m
      takeSpine n (SI.Two sa1 sa2 m)
        = SI.Two sa1 sa2 $ takeSpine (n - 1) m
      takeSpine n (SI.Three sa1 sa2 sa3 m)
        = SI.Three sa1 sa2 sa3 $ takeSpine (n - 1) m
-}


prop_identityA :: [A] -> Property
prop_identityA lst = toList (fromList lst) === lst

prop_identityB :: Stack A -> Property
prop_identityB stk = fromList (toList stk) === stk

--prop_identityC :: [A] -> Property
--prop_identityC lst = toList (fromListN (length lst) lst) === lst

--prop_identityD :: Stack A -> Property
--prop_identityD stk = fromListN (length stk) (toList stk) === stk

prop_cons :: A -> Stack A -> Property
prop_cons x xs = toList (x :< xs) === x : toList xs

prop_uncons :: Stack A -> Property
prop_uncons xs = case xs of
  Empty -> toList xs === []
  y :< ys -> toList xs === y : toList ys

prop_uncons_of_empty :: Property
prop_uncons_of_empty = uncons (Empty @(Stack A)) === Nothing

prop_uncons_of_cons :: A -> Stack A -> Property
prop_uncons_of_cons x xs = uncons (x :< xs) === Just (x, xs)

--prop_append :: Stack A -> Stack A -> Property
--prop_append xs ys = toList (xs <> ys) === toList xs ++ toList ys

--prop_compareLength :: Int -> Stack () -> Property
--prop_compareLength n s = compareLength n s === compare n (length s)

--prop_take :: Int -> Stack A -> Property
--prop_take n s = toList (S.take n s) === P.take n (toList s)

return [] -- This makes sure the above properties are seen by $allProperties
all_props :: TestTree
all_props = testProperties "properties" $allProperties

main :: IO ()
main = defaultMain all_props
