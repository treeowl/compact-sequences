{-# language CPP #-}
{-# language BangPatterns, ScopedTypeVariables, UnboxedTuples, MagicHash #-}
{-# language DeriveTraversable, StandaloneDeriving #-}
{-# language DataKinds #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{- OPTIONS_GHC -Wall #-}
{- OPTIONS_GHC -ddump-simpl #-}

module Data.CompactSequence.Deque.Internal where
import qualified Data.CompactSequence.Internal.Array as A
import Data.CompactSequence.Internal.Array (Array, Size (..), Mult (..))
import qualified Data.CompactSequence.Internal.Numbers as N
import qualified Data.Foldable as F
import Control.Monad.Trans.State.Strict
import Data.Function (on)

data Deque n a
  = Empty
  | Shallow !(Array n a)
  | Deep11 !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a)
  | Deep12 !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a)
  | Deep13 !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a)
  | Deep14 !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a) !(Array n a)

  | Deep21 !(Array n a) !(Array n a) 
           !(Deque ('Twice n) a)
           !(Array n a)
  | Deep22 !(Array n a) !(Array n a) 
           (Deque ('Twice n) a)
           !(Array n a) !(Array n a) 
  | Deep23 !(Array n a) !(Array n a) 
           (Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a)
  | Deep24 !(Array n a) !(Array n a) 
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a) !(Array n a)

  | Deep31 !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a)
  | Deep32 !(Array n a) !(Array n a) !(Array n a)
           (Deque ('Twice n) a)
           !(Array n a) !(Array n a) 
  | Deep33 !(Array n a) !(Array n a) !(Array n a)
           (Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a)
  | Deep34 !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a) !(Array n a)

  | Deep41 !(Array n a) !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a)
  | Deep42 !(Array n a) !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) 
  | Deep43 !(Array n a) !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a)
  | Deep44 !(Array n a) !(Array n a) !(Array n a) !(Array n a)
           !(Deque ('Twice n) a)
           !(Array n a) !(Array n a) !(Array n a) !(Array n a)
  deriving (Functor, Foldable, Traversable)

instance Eq a => Eq (Deque n a) where
  (==) = (==) `on` F.toList

instance Ord a => Ord (Deque n a) where
  compare = compare `on` F.toList

empty :: Deque n a
empty = Empty

consA :: Size n -> Array n a -> Deque n a -> Deque n a
consA !_ !sa Empty = Shallow sa
consA !_ !sa1 (Shallow sa2) = Deep11 sa1 Empty sa2

consA !_ !x (Deep11 sa m ta)
  = Deep21 x sa m ta
consA !_ !x (Deep12 sa m ta1 ta2)
  = Deep22 x sa m ta1 ta2
consA !_ !x (Deep13 sa m ta1 ta2 ta3)
  = Deep23 x sa m ta1 ta2 ta3
consA !_ !x (Deep14 sa m ta1 ta2 ta3 ta4)
  = Deep24 x sa m ta1 ta2 ta3 ta4

consA !_ !x (Deep21 sa1 sa2 m ta)
  = Deep31 x sa1 sa2 m ta
consA !_ !x (Deep22 sa1 sa2 m ta1 ta2)
  = Deep32 x sa1 sa2 m ta1 ta2
consA !_ !x (Deep23 sa1 sa2 m ta1 ta2 ta3)
  = Deep33 x sa1 sa2 m ta1 ta2 ta3
consA !_ !x (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4)
  = Deep34 x sa1 sa2 m ta1 ta2 ta3 ta4

consA !_ !x (Deep31 sa1 sa2 sa3 m ta)
  = Deep41 x sa1 sa2 sa3 m ta
consA !_ !x (Deep32 sa1 sa2 sa3 m ta1 ta2)
  = Deep42 x sa1 sa2 sa3 m ta1 ta2
consA !_ !x (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3)
  = Deep43 x sa1 sa2 sa3 m ta1 ta2 ta3
consA !_ !x (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4)
  = Deep44 x sa1 sa2 sa3 m ta1 ta2 ta3 ta4

consA !n !x (Deep41 sa1 sa2 sa3 sa4 m ta)
  | ShiftedR m' me1 me2 <- shiftRA n sa3 sa4 m
  = Deep33 x sa1 sa2 m' me1 me2 ta
consA !n !x (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2)
  = Deep32 x sa1 sa2 (consA (A.twice n) (A.append n sa3 sa4) m) ta1 ta2
consA !n !x (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3)
  = Deep33 x sa1 sa2 (consA (A.twice n) (A.append n sa3 sa4) m) ta1 ta2 ta3
consA !n !x (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)
  = Deep32 x sa1 sa2 (consSnocA (A.twice n) (A.append n sa3 sa4) m (A.append n ta1 ta2)) ta3 ta4

snocA :: Size n -> Deque n a -> Array n a -> Deque n a
snocA !_ Empty x = Shallow x
snocA !_ (Shallow sa) x = Deep11 sa Empty x

snocA !_ (Deep11 sa m ta) x
  = Deep12 sa m ta x
snocA !_ (Deep21 sa1 sa2 m ta) x
  = Deep22 sa1 sa2 m ta x
snocA !_ (Deep31 sa1 sa2 sa3 m ta) x
  = Deep32 sa1 sa2 sa3 m ta x
snocA !_ (Deep41 sa1 sa2 sa3 sa4 m ta) x
  = Deep42 sa1 sa2 sa3 sa4 m ta x

snocA !_ (Deep12 sa m ta1 ta2) x
  = Deep13 sa m ta1 ta2 x
snocA !_ (Deep22 sa1 sa2 m ta1 ta2) x
  = Deep23 sa1 sa2 m ta1 ta2 x
snocA !_ (Deep32 sa1 sa2 sa3 m ta1 ta2) x
  = Deep33 sa1 sa2 sa3 m ta1 ta2 x
snocA !_ (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2) x
  = Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 x

snocA !_ (Deep13 sa m ta1 ta2 ta3) x
  = Deep14 sa m ta1 ta2 ta3 x
snocA !_ (Deep23 sa1 sa2 m ta1 ta2 ta3) x
  = Deep24 sa1 sa2 m ta1 ta2 ta3 x
snocA !_ (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3) x
  = Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 x
snocA !_ (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3) x
  = Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 x

snocA !n (Deep14 sa1 m ta1 ta2 ta3 ta4) x
  | ShiftedL mb1 mb2 m' <- shiftLA n m ta1 ta2
  = Deep33 sa1 mb1 mb2 m' ta3 ta4 x
snocA !n (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4) x
  = Deep23 sa1 sa2 (snocA (A.twice n) m (A.append n ta1 ta2)) ta3 ta4 x
snocA !n (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4) x
  = Deep33 sa1 sa2 sa3 (snocA (A.twice n) m (A.append n ta1 ta2)) ta3 ta4 x
snocA !n (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4) x
  = Deep23 sa1 sa2
           (consSnocA (A.twice n)
                      (A.append n sa3 sa4)
                      m
                      (A.append n ta1 ta2))
           ta3 ta4 x

data ViewL n a
  = EmptyL
  | ConsL !(Array n a) (Deque n a)

data ViewR n a
  = EmptyR
  | SnocR (Deque n a) !(Array n a)

viewLA :: Size n -> Deque n a -> ViewL n a
viewLA !_ Empty = EmptyL
viewLA !_ (Shallow sa) = ConsL sa Empty

viewLA !_ (Deep41 sa1 sa2 sa3 sa4 m ta1)
  = ConsL sa1 (Deep31 sa2 sa3 sa4 m ta1)
viewLA !_ (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2)
  = ConsL sa1 (Deep32 sa2 sa3 sa4 m ta1 ta2)
viewLA !_ (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3)
  = ConsL sa1 (Deep33 sa2 sa3 sa4 m ta1 ta2 ta3)
viewLA !_ (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)
  = ConsL sa1 (Deep34 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)

viewLA !_ (Deep31 sa1 sa2 sa3 m ta1)
  = ConsL sa1 (Deep21 sa2 sa3 m ta1)
viewLA !_ (Deep32 sa1 sa2 sa3 m ta1 ta2)
  = ConsL sa1 (Deep22 sa2 sa3 m ta1 ta2)
viewLA !_ (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3)
  = ConsL sa1 (Deep23 sa2 sa3 m ta1 ta2 ta3)
viewLA !_ (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4)
  = ConsL sa1 (Deep24 sa2 sa3 m ta1 ta2 ta3 ta4)

viewLA !_ (Deep21 sa1 sa2 m ta1)
  = ConsL sa1 (Deep11 sa2 m ta1)
viewLA !_ (Deep22 sa1 sa2 m ta1 ta2)
  = ConsL sa1 (Deep12 sa2 m ta1 ta2)
viewLA !_ (Deep23 sa1 sa2 m ta1 ta2 ta3)
  = ConsL sa1 (Deep13 sa2 m ta1 ta2 ta3)
viewLA !_ (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4)
  = ConsL sa1 (Deep14 sa2 m ta1 ta2 ta3 ta4)

viewLA !n (Deep11 sa1 m ta1)
  = ConsL sa1 $ case unconsUnsnocA (A.twice n) m of
      EmptyUCUS -> Shallow ta1
      OneUCUS mb
        | (mb1, mb2) <- A.splitArray n mb
        -> Deep21 mb1 mb2 Empty ta1
      UCUS mb m' me
        | (mb1, mb2) <- A.splitArray n mb
        , (me1, me2) <- A.splitArray n me
        -> Deep23 mb1 mb2 m' me1 me2 ta1
viewLA !n (Deep12 sa1 m ta1 ta2)
  = ConsL sa1 $ case viewLA (A.twice n) m of
      EmptyL -> Deep11 ta1 Empty ta2
      ConsL mb m'
        | (mb1, mb2) <- A.splitArray n mb
        -> Deep22 mb1 mb2 m' ta1 ta2
viewLA !n (Deep13 sa1 m ta1 ta2 ta3)
  = ConsL sa1 $ case viewLA (A.twice n) m of
      EmptyL -> Deep21 ta1 ta2 Empty ta3
      ConsL mb m'
        | (mb1, mb2) <- A.splitArray n mb
        -> Deep23 mb1 mb2 m' ta1 ta2 ta3
viewLA !n (Deep14 sa1 m ta1 ta2 ta3 ta4)
  = ConsL sa1 $ case shiftLA n m ta1 ta2 of
      ShiftedL mb1 mb2 m' -> Deep22 mb1 mb2 m' ta3 ta4

viewRA :: Size n -> Deque n a -> ViewR n a
viewRA !_ Empty = EmptyR
viewRA !_ (Shallow sa) = SnocR Empty sa

viewRA !_ (Deep14 sa1 m ta1 ta2 ta3 ta4)
  = SnocR (Deep13 sa1 m ta1 ta2 ta3) ta4
viewRA !_ (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4)
  = SnocR (Deep23 sa1 sa2 m ta1 ta2 ta3) ta4
viewRA !_ (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4)
  = SnocR (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3) ta4
viewRA !_ (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)
  = SnocR (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3) ta4

viewRA !_ (Deep13 sa1 m ta1 ta2 ta3)
  = SnocR (Deep12 sa1 m ta1 ta2) ta3
viewRA !_ (Deep23 sa1 sa2 m ta1 ta2 ta3)
  = SnocR (Deep22 sa1 sa2 m ta1 ta2) ta3
viewRA !_ (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3)
  = SnocR (Deep32 sa1 sa2 sa3 m ta1 ta2) ta3
viewRA !_ (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3)
  = SnocR (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2) ta3

viewRA !_ (Deep12 sa1 m ta1 ta2)
  = SnocR (Deep11 sa1 m ta1) ta2
viewRA !_ (Deep22 sa1 sa2 m ta1 ta2)
  = SnocR (Deep21 sa1 sa2 m ta1) ta2
viewRA !_ (Deep32 sa1 sa2 sa3 m ta1 ta2)
  = SnocR (Deep31 sa1 sa2 sa3 m ta1) ta2
viewRA !_ (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2)
  = SnocR (Deep41 sa1 sa2 sa3 sa4 m ta1) ta2

viewRA !n (Deep11 sa1 m ta1)
  = flip SnocR ta1 $ case unconsUnsnocA (A.twice n) m of
      EmptyUCUS -> Shallow sa1
      OneUCUS mb
        | (m1, m2) <- A.splitArray n mb
        -> Deep21 sa1 m1 Empty m2
      UCUS mb m' me
        | (mb1, mb2) <- A.splitArray n mb
        , (me1, me2) <- A.splitArray n me
        -> Deep32 sa1 mb1 mb2 m' me1 me2
viewRA !n (Deep21 sa1 sa2 m ta1)
  = flip SnocR ta1 $ case viewRA (A.twice n) m of
      EmptyR -> Deep11 sa1 Empty sa2
      SnocR m' me
        | (me1, me2) <- A.splitArray n me
        -> Deep22 sa1 sa2 m' me1 me2
viewRA !n (Deep31 sa1 sa2 sa3 m ta1)
  = flip SnocR ta1 $ case viewRA (A.twice n) m of
      EmptyR -> Deep21 sa1 sa2 Empty sa3
      SnocR m' me
        | (me1, me2) <- A.splitArray n me
        -> Deep32 sa1 sa2 sa3 m' me1 me2
viewRA !n (Deep41 sa1 sa2 sa3 sa4 m ta1)
  = flip SnocR ta1 $ case shiftRA n sa3 sa4 m of
      ShiftedR m' me1 me2 -> Deep22 sa1 sa2 m' me1 me2

data ShiftedL n a = ShiftedL !(Array n a) !(Array n a) (Deque ('Twice n) a)
data ShiftedR n a = ShiftedR (Deque ('Twice n) a) !(Array n a) !(Array n a)

shiftLA :: Size n -> Deque ('Twice n) a -> Array n a -> Array n a -> ShiftedL n a
shiftLA !_ Empty !sa1 !sa2 = ShiftedL sa1 sa2 Empty
shiftLA !n (Shallow sa) !ta1 !ta2
  = shriftL n sa (Shallow (A.append n ta1 ta2))

shiftLA !n (Deep11 sa1 m ta1) !x !y
  = shriftL n sa1 $ case viewLA (A.twice (A.twice n)) m of
      EmptyL -> Deep11 ta1 Empty (A.append n x y)
      ConsL mb m'
        | (mb1, mb2) <- A.splitArray (A.twice n) mb
        -> Deep22 mb1 mb2 m' ta1 (A.append n x y)
shiftLA !n (Deep12 sa1 m ta1 ta2) !x !y
  = shriftL n sa1 $ case viewLA (A.twice (A.twice n)) m of
      EmptyL -> Deep21 ta1 ta2 Empty (A.append n x y)
      ConsL mb m'
        | (mb1, mb2) <- A.splitArray (A.twice n) mb
        -> Deep23 mb1 mb2 m' ta1 ta2 (A.append n x y)
shiftLA !n (Deep13 sa1 m ta1 ta2 ta3) !x !y
  = shriftL n sa1 $ case shiftLA (A.twice n) m ta1 ta2 of
      ShiftedL mb1 mb2 m' -> Deep22 mb1 mb2 m' ta3 (A.append n x y)
shiftLA !n (Deep14 sa1 m ta1 ta2 ta3 ta4) !x !y
  = shriftL n sa1 $ case shiftLA (A.twice n) m ta1 ta2 of
      ShiftedL mb1 mb2 m' -> Deep23 mb1 mb2 m' ta3 ta4 (A.append n x y)

shiftLA !n (Deep21 sa1 sa2 m ta1) !x !y
  = shriftL n sa1 $ Deep12 sa2 m ta1 (A.append n x y)
shiftLA !n (Deep22 sa1 sa2 m ta1 ta2) !x !y
  = shriftL n sa1 $ Deep13 sa2 m ta1 ta2 (A.append n x y)
shiftLA !n (Deep23 sa1 sa2 m ta1 ta2 ta3) !x !y
  = shriftL n sa1 $ Deep14 sa2 m ta1 ta2 ta3 (A.append n x y)
shiftLA !n (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4) !x !y
  = shriftL n sa1 $ case shiftLA (A.twice n) m ta1 ta2 of
      ShiftedL mb1 mb2 m' -> Deep33 sa2 mb1 mb2 m' ta3 ta4 (A.append n x y)

shiftLA !n (Deep31 sa1 sa2 sa3 m ta1) !x !y
  = shriftL n sa1 $ Deep22 sa2 sa3 m ta1 (A.append n x y)
shiftLA !n (Deep32 sa1 sa2 sa3 m ta1 ta2) !x !y
  = shriftL n sa1 $ Deep23 sa2 sa3 m ta1 ta2 (A.append n x y)
shiftLA !n (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3) !x !y
  = shriftL n sa1 $ Deep24 sa2 sa3 m ta1 ta2 ta3 (A.append n x y)
shiftLA !n (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4) !x !y
  = shriftL n sa1 $
      Deep23 sa2 sa3
             (snocA (A.twice (A.twice n)) m (A.append (A.twice n) ta1 ta2))
             ta3 ta4 (A.append n x y)

shiftLA !n (Deep41 sa1 sa2 sa3 sa4 m ta1) !x !y
  = shriftL n sa1 $ Deep32 sa2 sa3 sa4 m ta1 (A.append n x y)
shiftLA !n (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2) !x !y
  = shriftL n sa1 $ Deep33 sa2 sa3 sa4 m ta1 ta2 (A.append n x y)
shiftLA !n (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3) !x !y
  = shriftL n sa1 $ Deep34 sa2 sa3 sa4 m ta1 ta2 ta3 (A.append n x y)
shiftLA !n (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4) !x !y
  = shriftL n sa1 $
      Deep33 sa2 sa3 sa4
             (snocA (A.twice (A.twice n)) m (A.append (A.twice n) ta1 ta2))
             ta3 ta4 (A.append n x y)

shriftL :: Size n -> Array ('A.Twice n) a -> Deque ('A.Twice n) a -> ShiftedL n a
shriftL !n !sa d
  | (sa1, sa2) <- A.splitArray n sa
  = ShiftedL sa1 sa2 d

shiftRA :: Size n -> Array n a -> Array n a -> Deque ('Twice n) a -> ShiftedR n a
shiftRA !_ !sa1 !sa2 Empty = ShiftedR Empty sa1 sa2
shiftRA n sa1 sa2 (Shallow ta)
  = shriftR n ta (Shallow (A.append n sa1 sa2))
shiftRA n x y (Deep11 sa1 m ta1)
  = shriftR n ta1 $ case viewRA (A.twice (A.twice n)) m of
      EmptyR -> Deep11 (A.append n x y) Empty sa1
      SnocR m' me
        | (me1, me2) <- A.splitArray (A.twice n) me
        -> Deep22 (A.append n x y) sa1 m' me1 me2
shiftRA n x y (Deep12 sa1 m ta1 ta2)
  = shriftR n ta2 $ Deep21 (A.append n x y) sa1 m ta1
shiftRA n x y (Deep13 sa1 m ta1 ta2 ta3)
  = shriftR n ta3 $ Deep22 (A.append n x y) sa1 m ta1 ta2
shiftRA n x y (Deep14 sa1 m ta1 ta2 ta3 ta4)
  = shriftR n ta4 $ Deep23 (A.append n x y) sa1 m ta1 ta2 ta3

shiftRA n x y (Deep21 sa1 sa2 m ta1)
  = shriftR n ta1 $ case viewRA (A.twice (A.twice n)) m of
      EmptyR -> Deep21 (A.append n x y) sa1 Empty sa2
      SnocR m' me
        | (me1, me2) <- A.splitArray (A.twice n) me
        -> Deep32 (A.append n x y) sa1 sa2 m' me1 me2
shiftRA n x y (Deep22 sa1 sa2 m ta1 ta2)
  = shriftR n ta2 $
      Deep31 (A.append n x y) sa1 sa2 m ta1
shiftRA n x y (Deep23 sa1 sa2 m ta1 ta2 ta3)
  = shriftR n ta3 $
      Deep32 (A.append n x y) sa1 sa2 m ta1 ta2
shiftRA n x y (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4)
  = shriftR n ta4 $
      Deep33 (A.append n x y) sa1 sa2 m ta1 ta2 ta3

shiftRA n x y (Deep31 sa1 sa2 sa3 m ta1)
  = shriftR n ta1 $ case shiftRA (A.twice n) sa2 sa3 m of
      ShiftedR m' me1 me2 -> Deep22 (A.append n x y) sa1 m' me1 me2
shiftRA n x y (Deep32 sa1 sa2 sa3 m ta1 ta2)
  = shriftR n ta2 $ Deep41 (A.append n x y) sa1 sa2 sa3 m ta1
shiftRA n x y (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3)
  = shriftR n ta3 $ Deep42 (A.append n x y) sa1 sa2 sa3 m ta1 ta2
shiftRA n x y (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4)
  = shriftR n ta4 $ Deep43 (A.append n x y) sa1 sa2 sa3 m ta1 ta2 ta3

shiftRA n x y (Deep41 sa1 sa2 sa3 sa4 m ta1)
  = shriftR n ta1 $ case shiftRA (A.twice n) sa3 sa4 m of
      ShiftedR m' me1 me2 -> Deep32 (A.append n x y) sa1 sa2 m' me1 me2
shiftRA n x y (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2)
  = shriftR n ta2 $ case shiftRA (A.twice n) sa3 sa4 m of
      ShiftedR m' me1 me2 -> Deep33 (A.append n x y) sa1 sa2 m' me1 me2 ta1
shiftRA n x y (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3)
  = shriftR n ta3 $
      Deep32 (A.append n x y) sa1 sa2
           (consA (A.twice (A.twice n)) (A.append (A.twice n) sa3 sa4) m)
           ta1 ta2
shiftRA n x y (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)
  = shriftR n ta4 $
      Deep33 (A.append n x y) sa1 sa2
           (consA (A.twice (A.twice n)) (A.append (A.twice n) sa3 sa4) m)
           ta1 ta2 ta3

shriftR :: Size n -> Array ('A.Twice n) a -> Deque ('A.Twice n) a -> ShiftedR n a
shriftR !n !sa d
  | (sa1, sa2) <- A.splitArray n sa
  = ShiftedR d sa1 sa2

consSnocA :: Size n -> Array n a -> Deque n a -> Array n a -> Deque n a
consSnocA !_ !sa1 Empty !sa2 = Deep11 sa1 Empty sa2
consSnocA !_ !sa1 (Shallow sa2) !sa3 = Deep21 sa1 sa2 Empty sa3
consSnocA !_ !x (Deep11 sa1 m ta1) !y
  = Deep22 x sa1 m ta1 y
consSnocA !_ !x (Deep12 sa1 m ta1 ta2) !y
  = Deep23 x sa1 m ta1 ta2 y
consSnocA !_ !x (Deep13 sa1 m ta1 ta2 ta3) !y
  = Deep24 x sa1 m ta1 ta2 ta3 y
consSnocA !n !x (Deep14 sa1 m ta1 ta2 ta3 ta4) !y
  = Deep23 x sa1 (snocA (A.twice n) m (A.append n ta1 ta2)) ta3 ta4 y

consSnocA !_ !x (Deep21 sa1 sa2 m ta1) !y
  = Deep32 x sa1 sa2 m ta1 y
consSnocA !_ !x (Deep22 sa1 sa2 m ta1 ta2) !y
  = Deep33 x sa1 sa2 m ta1 ta2 y
consSnocA !_ !x (Deep23 sa1 sa2 m ta1 ta2 ta3) !y
  = Deep34 x sa1 sa2 m ta1 ta2 ta3 y
consSnocA !n !x (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4) !y
  = Deep33 x sa1 sa2 (snocA (A.twice n) m (A.append n ta1 ta2)) ta3 ta4 y

consSnocA !_ !x (Deep31 sa1 sa2 sa3 m ta1) !y
  = Deep42 x sa1 sa2 sa3 m ta1 y
consSnocA !_ !x (Deep32 sa1 sa2 sa3 m ta1 ta2) !y
  = Deep43 x sa1 sa2 sa3 m ta1 ta2 y
consSnocA !_ !x (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3) !y
  = Deep44 x sa1 sa2 sa3 m ta1 ta2 ta3 y
consSnocA !n !x (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4) !y
  = Deep23 x sa1
           (consSnocA (A.twice n) (A.append n sa2 sa3) m (A.append n ta1 ta2))
           ta3 ta4 y

consSnocA n !x (Deep41 sa1 sa2 sa3 sa4 m ta1) !y
  = Deep32 x sa1 sa2 (consA (A.twice n) (A.append n sa3 sa4) m) ta1 y
consSnocA n !x (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2) !y
  = Deep33 x sa1 sa2 (consA (A.twice n) (A.append n sa3 sa4) m) ta1 ta2 y
consSnocA n !x (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3) !y
  = Deep32 x sa1 sa2 (consSnocA (A.twice n) (A.append n sa3 sa4) m (A.append n ta1 ta2)) ta3 y
consSnocA n !x (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4) !y
  = Deep33 x sa1 sa2 (consSnocA (A.twice n) (A.append n sa3 sa4) m (A.append n ta1 ta2)) ta3 ta4 y

data UCUS n a
  = EmptyUCUS
  | OneUCUS !(Array n a)
  | UCUS !(Array n a) (Deque n a) !(Array n a)

unconsUnsnocA :: Size n -> Deque n a -> UCUS n a
unconsUnsnocA !_ Empty = EmptyUCUS
unconsUnsnocA !_ (Shallow sa) = OneUCUS sa
unconsUnsnocA n (Deep11 sa1 m ta1)
  = flip (UCUS sa1) ta1 $
      case unconsUnsnocA (A.twice n) m of
        EmptyUCUS -> Empty
        OneUCUS mm
          | (m1, m2) <- A.splitArray n mm
          -> Deep11 m1 Empty m2
        UCUS mb m' me
          | (mb1, mb2) <- A.splitArray n mb
          , (me1, me2) <- A.splitArray n me
          -> Deep22 mb1 mb2 m' me1 me2
unconsUnsnocA n (Deep12 sa1 m ta1 ta2)
  = flip (UCUS sa1) ta2 $
      case unconsUnsnocA (A.twice n) m of
        EmptyUCUS -> Shallow ta1
        OneUCUS mm
          | (m1, m2) <- A.splitArray n mm
          -> Deep21 m1 m2 Empty ta1
        UCUS mb m' me
          | (mb1, mb2) <- A.splitArray n mb
          , (me1, me2) <- A.splitArray n me
          -> Deep23 mb1 mb2 m' me1 me2 ta1
unconsUnsnocA n (Deep13 sa1 m ta1 ta2 ta3)
  = flip (UCUS sa1) ta3 $
      case viewLA (A.twice n) m of
        EmptyL -> Deep11 ta1 Empty ta2
        ConsL mb m'
          | (mb1, mb2) <- A.splitArray n mb
          -> Deep22 mb1 mb2 m' ta1 ta2
unconsUnsnocA n (Deep14 sa1 m ta1 ta2 ta3 ta4)
  = flip (UCUS sa1) ta4 $
      case viewLA (A.twice n) m of
        EmptyL -> Deep12 ta1 Empty ta2 ta3
        ConsL mb m'
          | (mb1, mb2) <- A.splitArray n mb
          -> Deep23 mb1 mb2 m' ta1 ta2 ta3

unconsUnsnocA !n (Deep21 sa1 sa2 m ta1)
  = flip (UCUS sa1) ta1 $
      case unconsUnsnocA (A.twice n) m of
        EmptyUCUS -> Shallow sa2
        OneUCUS mm
          | (m1, m2) <- A.splitArray n mm
          -> Deep21 sa2 m1 Empty m2
        UCUS mb m' me
          | (mb1, mb2) <- A.splitArray n mb
          , (me1, me2) <- A.splitArray n me
          -> Deep32 sa2 mb1 mb2 m' me1 me2
unconsUnsnocA !_ (Deep22 sa1 sa2 m ta1 ta2)
  = UCUS sa1 (Deep11 sa2 m ta1) ta2
unconsUnsnocA !_ (Deep23 sa1 sa2 m ta1 ta2 ta3)
  = UCUS sa1 (Deep12 sa2 m ta1 ta2) ta3
unconsUnsnocA !_ (Deep24 sa1 sa2 m ta1 ta2 ta3 ta4)
  = UCUS sa1 (Deep13 sa2 m ta1 ta2 ta3) ta4

unconsUnsnocA !n (Deep31 sa1 sa2 sa3 m ta1)
  = flip (UCUS sa1) ta1 $
      case viewRA (A.twice n) m of
        EmptyR -> Deep11 sa2 Empty sa3
        SnocR m' me
          | (me1, me2) <- A.splitArray n me
          -> Deep22 sa2 sa3 m' me1 me2
unconsUnsnocA !_ (Deep32 sa1 sa2 sa3 m ta1 ta2)
  = UCUS sa1 (Deep21 sa2 sa3 m ta1) ta2
unconsUnsnocA !_ (Deep33 sa1 sa2 sa3 m ta1 ta2 ta3)
  = UCUS sa1 (Deep22 sa2 sa3 m ta1 ta2) ta3
unconsUnsnocA !_ (Deep34 sa1 sa2 sa3 m ta1 ta2 ta3 ta4)
  = UCUS sa1 (Deep23 sa2 sa3 m ta1 ta2 ta3) ta4

unconsUnsnocA !n (Deep41 sa1 sa2 sa3 sa4 m ta1)
  = flip (UCUS sa1) ta1 $
      case viewRA (A.twice n) m of
        EmptyR -> Deep21 sa2 sa3 Empty sa4
        SnocR m' me
          | (me1, me2) <- A.splitArray n me
          -> Deep32 sa2 sa3 sa4 m' me1 me2
unconsUnsnocA !_ (Deep42 sa1 sa2 sa3 sa4 m ta1 ta2)
  = UCUS sa1 (Deep31 sa2 sa3 sa4 m ta1) ta2
unconsUnsnocA !_ (Deep43 sa1 sa2 sa3 sa4 m ta1 ta2 ta3)
  = UCUS sa1 (Deep32 sa2 sa3 sa4 m ta1 ta2) ta3
unconsUnsnocA !_ (Deep44 sa1 sa2 sa3 sa4 m ta1 ta2 ta3 ta4)
  = UCUS sa1 (Deep33 sa2 sa3 sa4 m ta1 ta2 ta3) ta4


data Deque_ n a
  = Empty_
  | Shallow_ !(Array n a)
  | Deep_ !(Digit n a) (Deque ('Twice n) a) !(Digit n a)

matchDeep :: Deque n a -> Deque_ n a
matchDeep q = case q of
  Empty -> Empty_
  Shallow sa -> Shallow_ sa
  Deep11 x m a -> Deep_ (One x) m (One a)
  Deep12 x m a b -> Deep_ (One x) m (Two a b)
  Deep13 x m a b c -> Deep_ (One x) m (Three a b c)
  Deep14 x m a b c d -> Deep_ (One x) m (Four a b c d)
  Deep21 x y m a -> Deep_ (Two x y) m (One a)
  Deep22 x y m a b -> Deep_ (Two x y) m (Two a b)
  Deep23 x y m a b c -> Deep_ (Two x y) m (Three a b c)
  Deep24 x y m a b c d -> Deep_ (Two x y) m (Four a b c d)
  Deep31 x y z m a -> Deep_ (Three x y z) m (One a)
  Deep32 x y z m a b -> Deep_ (Three x y z) m (Two a b)
  Deep33 x y z m a b c -> Deep_ (Three x y z) m (Three a b c)
  Deep34 x y z m a b c d -> Deep_ (Three x y z) m (Four a b c d)
  Deep41 x y z w m a -> Deep_ (Four x y z w) m (One a)
  Deep42 x y z w m a b -> Deep_ (Four x y z w) m (Two a b)
  Deep43 x y z w m a b c -> Deep_ (Four x y z w) m (Three a b c)
  Deep44 x y z w m a b c d -> Deep_ (Four x y z w) m (Four a b c d)
{-# INLINE matchDeep #-}

pattern Deep :: Digit n a -> Deque ('Twice n) a -> Digit n a -> Deque n a
pattern Deep pr m sf <- (matchDeep -> Deep_ pr m sf)
  where
    Deep (One x) m (One a) = Deep11 x m a
    Deep (One x) m (Two a b) = Deep12 x m a b
    Deep (One x) m (Three a b c) = Deep13 x m a b c
    Deep (One x) m (Four a b c d) = Deep14 x m a b c d
    Deep (Two x y) m (One a) = Deep21 x y m a
    Deep (Two x y) m (Two a b) = Deep22 x y m a b
    Deep (Two x y) m (Three a b c) = Deep23 x y m a b c
    Deep (Two x y) m (Four a b c d) = Deep24 x y m a b c d
    Deep (Three x y z) m (One a) = Deep31 x y z m a
    Deep (Three x y z) m (Two a b) = Deep32 x y z m a b
    Deep (Three x y z) m (Three a b c) = Deep33 x y z m a b c
    Deep (Three x y z) m (Four a b c d) = Deep34 x y z m a b c d

    Deep (Four x y z w) m (One a) = Deep41 x y z w m a
    Deep (Four x y z w) m (Two a b) = Deep42 x y z w m a b
    Deep (Four x y z w) m (Three a b c) = Deep43 x y z w m a b c
    Deep (Four x y z w) m (Four a b c d) = Deep44 x y z w m a b c d

{-# COMPLETE Empty, Shallow, Deep #-}

data Digit n a
  = One !(Array n a)
  | Two !(Array n a) !(Array n a)
  | Three !(Array n a) !(Array n a) !(Array n a)
  | Four !(Array n a) !(Array n a) !(Array n a) !(Array n a)

-- Converts a list of sz * n elements to a deque.
-- Unlike a queue, we *can't* convert incrementally,
-- so there's not much use being polymorphic in the state
-- monad.
fromListNM :: Size sz -> Int -> State [a] (Deque sz a)
fromListNM sz n = fromListNS sz (N.toBin45 n)

fromListNS :: Size sz -> N.Bin45 -> State [a] (Deque sz a)
fromListNS !_ N.End45 = pure Empty
fromListNS sz N.OneEnd45 = do
  sa1 <- state (A.arraySplitListN sz)
  pure $! Shallow sa1
fromListNS sz N.TwoEnd45 = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  pure $! Deep11 sa1 Empty sa2
fromListNS sz N.ThreeEnd45 = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  sa3 <- state (A.arraySplitListN sz)
  pure $! Deep21 sa1 sa2 Empty sa3
fromListNS sz (N.Four45 n) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  m <- fromListNS (A.twice sz) n
  ta1 <- state (A.arraySplitListN sz)
  ta2 <- state (A.arraySplitListN sz)
  pure $ Deep22 sa1 sa2 m ta1 ta2
fromListNS sz (N.Five45 n) = do
  sa1 <- state (A.arraySplitListN sz)
  sa2 <- state (A.arraySplitListN sz)
  sa3 <- state (A.arraySplitListN sz)
  m <- fromListNS (A.twice sz) n
  ta1 <- state (A.arraySplitListN sz)
  ta2 <- state (A.arraySplitListN sz)
  pure $ Deep32 sa1 sa2 sa3 m ta1 ta2
