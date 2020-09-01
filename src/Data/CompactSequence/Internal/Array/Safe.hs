{-# language MagicHash #-}
{-# language Trustworthy #-}

module Data.CompactSequence.Internal.Array.Safe
  ( Array
  , singleton
  , getSingleton#
  , getSingletonA
  , mk2
  , get2#
  , get2A
  , mk4
  , get4#
  , get4A
  , arrayToSmallArray
  , splitArray
  , append
  , arraySplitListN
  , fromList
  ) where
import Data.CompactSequence.Internal.Array
