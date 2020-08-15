module Data.CompactSequence.Internal.Numbers where
import Data.Bits

-- A representation of 1-2 binary numbers. We use this to build stacks or stack
-- fragments of known size.
data Dyadic = DOne !Dyadic | DTwo !Dyadic | DEnd
  deriving (Eq, Show)

toDyadic :: Int -> Dyadic
toDyadic n0 = go (n0 + 1)
  where
    go 1 = DEnd
    go n = case n .&. 1 of
      0 -> DOne $ go (unsafeShiftR n 1)
      _ -> DTwo $ go (unsafeShiftR n 1)
{-# NOINLINE toDyadic #-}

{-
-- We'll have to figure out how to write something
-- like this to append stacks more efficiently.
incDyadic :: Dyadic -> Dyadic
incDyadic DEnd = DOne DEnd
incDyadic (DOne n) = DTwo n
incDyadic (DTwo n) = DOne (incDyadic n)

addDyadic :: Dyadic -> Dyadic -> Dyadic
addDyadic = go 0
  where
    go 0 DEnd !n = n
    go 1 DEnd !n = incDyadic n
    go _ DEnd !n = incDyadic (incDyadic n)
    go !c !n DEnd = go c DEnd n
    go !c 
-}

-- A representation of 2-3 binary numbers, where the most significant digit may
-- also be 1. We use this to build stacks or stack fragments of known size.
data Bin23 = Two23 !Bin23 | Three23 !Bin23 | End23 | OneEnd23
  deriving (Eq, Show)

toBin23 :: Int -> Bin23
toBin23 n0 = go (n0 + 2)
  where
    go 2 = End23
    go 3 = OneEnd23
    go n = case n .&. 1 of
      0 -> Two23 $ go (unsafeShiftR n 1)
      _ -> Three23 $ go (unsafeShiftR n 1)
{-# NOINLINE toBin23 #-}
