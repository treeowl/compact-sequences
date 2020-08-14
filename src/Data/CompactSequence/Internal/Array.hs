{-# language DataKinds #-}
{-# language TypeOperators #-}
{-# language KindSignatures #-}
{-# language BangPatterns #-}
{-# language RoleAnnotations #-}
{-# language MagicHash #-}
{-# language UnboxedTuples #-}
{-# language NoStarIsType #-}
{-# language RankNTypes #-}
{-# language DeriveTraversable #-}
{-# language Unsafe #-}

module Data.CompactSequence.Internal.Array where
import Data.Primitive.SmallArray
import Control.Monad.ST.Strict

data Mult = Twice Mult | Mul1

newtype Array (n :: Mult) a = Array (SmallArray a)
  deriving (Functor, Foldable, Traversable)
type role Array nominal representational

newtype Size (n :: Mult) = Size Int
type role Size nominal

getSize :: Size n -> Int
getSize (Size n) = n

--halve :: Size (Twice m) -> Size m
--halve (Size n) = Size (n `quot` 2)

one :: Size Mul1
one = Size 1

twice :: Size n -> Size (Twice n)
twice (Size n) = Size (2*n)

singleton :: a -> Array Mul1 a
singleton x = Array (pure x)

-- | Unsafely convert a 'SmallArray' of size @n@
-- to an @'Array' n@. This is genuinely unsafe: if
-- @n@ is greater than the true array size, then
-- some operation will eventually violate memory safety.
unsafeSmallArrayToArray :: SmallArray a -> Array n a
unsafeSmallArrayToArray = Array

arrayToSmallArray :: Array n a -> SmallArray a
arrayToSmallArray (Array sa) = sa

getSingleton# :: Array Mul1 a -> (# a #)
getSingleton# (Array sa) = indexSmallArray## sa 0

getSingletonA :: Applicative f => Array Mul1 a -> f a
getSingletonA (Array sa)
  | (# a #) <- indexSmallArray## sa 0
  = pure a

splitArray :: Size n -> Array (Twice n) a -> (Array n a, Array n a)
splitArray (Size len) (Array sa1) = (Array sa2, Array sa3)
  where
    !sa2 = cloneSmallArray sa1 0 len
    !sa3 = cloneSmallArray sa1 len len

-- | Append two arrays of the same size. We take the size
-- of the argument arrays so we can build the result array
-- before loading the first argument array into cache. Is
-- this the right approach? Not sure. We *certainly* don't
-- want to just use `<>`, because 
append :: Size n -> Array n a -> Array n a -> Array (Twice n) a
append (Size n) (Array xs) (Array ys) = Array $
    createSmallArray (2*n)
      (error "Data.CompactSequence.Internal.Array.append: Internal error")
      $ \sma -> copySmallArray sma 0 xs 0 n
        *> copySmallArray sma n ys 0 n

-- Shamelessly stolen from primitive.
createSmallArray
  :: Int
  -> a
  -> (forall s. SmallMutableArray s a -> ST s ())
  -> SmallArray a
createSmallArray n x f = runSmallArray $ do
  mary <- newSmallArray n x
  f mary
  pure mary

arraySplitListN :: Size n -> [a] -> (Array n a, [a])
arraySplitListN (Size n) xs
  | (sa, xs') <- smallArraySplitListN n xs
  = (Array sa, xs')

smallArraySplitListN :: Int -> [a] -> (SmallArray a, [a])
smallArraySplitListN n l = runST $ do
  sma <- newSmallArray n (error "smallArraySplitListN: uninitialized")
  let go !ix [] = if ix == n
        then do
          sa <- unsafeFreezeSmallArray sma
          pure (sa, [])
        else error "smallArraySplitListN: list length less than specified size"
      go !ix xss@(x : xs) = if ix < n
        then do
          writeSmallArray sma ix x
          go (ix+1) xs
        else do
          sa <- unsafeFreezeSmallArray sma
          pure (sa, xss)
  go 0 l

fromList :: Size n -> [a] -> Array n a
fromList (Size n) xs = Array (smallArrayFromListN n xs)
