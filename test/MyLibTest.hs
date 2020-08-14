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

import Data.CompactSequence.Stack.Simple.Internal
import qualified Data.CompactSequence.Stack.Internal as SI
import qualified Data.CompactSequence.Internal.Array.Safe as A

instance Arbitrary a => Arbitrary (Stack a) where
  arbitrary = sized $ \sz0 -> do
    sz <- choose (0, sz0)
    Stack <$> go A.one sz
    where
      go :: A.Size n -> Int -> Gen (SI.Stack n a)
      go !_ars n
        | n <= 0 = pure SI.Empty
      go !ars n = choose (1,3 :: Int) >>= \case
        1 -> SI.One <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> go (A.twice ars) (n - A.getSize ars)
        2 -> SI.Two <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                    <*> go (A.twice ars) (n - 2 * A.getSize ars)
        3 -> SI.Three <$> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                      <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                      <*> (A.fromList ars <$> vectorOf (A.getSize ars) arbitrary)
                      <*> go (A.twice ars) (n - 3 * A.getSize ars)


prop_identityA :: [A] -> Property
prop_identityA lst = toList (fromList lst) === lst

prop_identityB :: Stack A -> Property
prop_identityB stk = fromList (toList stk) === stk

prop_identityC :: [A] -> Property
prop_identityC lst = toList (fromListN (length lst) lst) === lst

prop_identityD :: Stack A -> Property
prop_identityD stk = fromListN (length stk) (toList stk) === stk

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

prop_append :: Stack A -> Stack A -> Property
prop_append xs ys = toList (xs <> ys) === toList xs ++ toList ys

return [] -- This makes sure the above properties are seen by $allProperties
all_props :: TestTree
all_props = testProperties "properties" $allProperties

main :: IO ()
main = defaultMain all_props
