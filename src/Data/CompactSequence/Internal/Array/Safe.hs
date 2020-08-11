{-# language MagicHash #-}
{-# language Trustworthy #-}

module Data.CompactSequence.Internal.Array.Safe
  ( Mult (..)
  , Array
  , Size
  , getSize
  , one
  , twice
  , singleton
  , getSingleton#
  , getSingletonA
  , arrayToSmallArray
  , splitArray
  , append
  , arraySplitListN
  ) where
import Data.CompactSequence.Internal.Array
