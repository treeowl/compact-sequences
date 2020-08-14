{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import           Data.Foldable
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.QuickCheck

import           Data.CompactSequence.Stack.Simple


prop_identity lst = toList (fromList lst) == lst


return [] -- This makes sure the above properties are seen by $allProperties
all_props :: TestTree
all_props = testProperties "properties" $allProperties

main :: IO ()
main = defaultMain all_props
