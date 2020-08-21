{-# language BangPatterns #-}
{-# language RoleAnnotations #-}
{-# language Safe #-}
{- OPTIONS_GHC -ddump-simpl #-}

{- |
Array sizes with phantom types. We use a very primitive
arrangement because that's all we need for now: the base
type is 'Sz1', 'Sz2', etc., and it's doubled as many times
as necessary by applying
the @Twice@ constructor. The base value is 'sz1', 'sz2',
etc., and it's doubled by applying the 'twice' function.
-}
module Data.CompactSequence.Internal.Size where

data Twice a
data Sz1
data Sz2
data Sz3
data Sz4
data Sz5
data Sz6
data Sz7
data Sz8
data Sz9
data Sz10
data Sz11
data Sz12
data Sz13
data Sz14
data Sz15
data Sz16
data Sz17
data Sz18
data Sz19

newtype Size n = Size Int
type role Size nominal

getSize :: Size n -> Int
getSize (Size n) = n

twice :: Size n -> Size (Twice n)
twice (Size n) = Size (2*n)

half :: Size (Twice m) -> Size m
half (Size n) = Size (n `quot` 2)

one :: Size Sz1
one = Size 1

sz1 :: Size Sz1
sz1 = Size 1

sz2 :: Size Sz2
sz2 = Size 2

sz3 :: Size Sz3
sz3 = Size 3

sz4 :: Size Sz4
sz4 = Size 4

sz5 :: Size Sz5
sz5 = Size 5

sz6 :: Size Sz6
sz6 = Size 6

sz7 :: Size Sz7
sz7 = Size 7

sz8 :: Size Sz8
sz8 = Size 8

sz9 :: Size Sz9
sz9 = Size 9

sz10 :: Size Sz10
sz10 = Size 10

sz11 :: Size Sz11
sz11 = Size 11

sz12 :: Size Sz12
sz12 = Size 12

sz13 :: Size Sz13
sz13 = Size 13

sz14 :: Size Sz14
sz14 = Size 14

sz15 :: Size Sz15
sz15 = Size 15

sz16 :: Size Sz16
sz16 = Size 16

sz17 :: Size Sz17
sz17 = Size 17

sz18 :: Size Sz18
sz18 = Size 18

sz19 :: Size Sz19
sz19 = Size 19
