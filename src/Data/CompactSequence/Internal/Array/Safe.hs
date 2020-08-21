{-# language MagicHash #-}
{-# language Trustworthy #-}

module Data.CompactSequence.Internal.Array.Safe
  ( Array
  , singleton
  , getSingleton#
  , getSingletonA
  , arrayToSmallArray
  , splitArray
  , append
  , arraySplitListN
  , fromList
  ) where
import Data.CompactSequence.Internal.Array
