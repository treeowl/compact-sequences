{-# language CPP #-}
{-# language BangPatterns, ScopedTypeVariables, UnboxedTuples, MagicHash #-}
{-# language DeriveTraversable, StandaloneDeriving #-}
{-# language DataKinds #-}
{-# OPTIONS_GHC -Wall #-}

module Data.CompactSequence.Deque.Internal where
import qualified Data.CompactSequence.Internal.Array as A
import Data.CompactSequence.Internal.Array (Array, Size, Mult (..))
import qualified Data.Foldable as F
import Data.Function (on)

data Deque n a
  = Empty
  | Shallow !(Array n a)
  | Deep !(Digit n a) (Deque ('Twice n) a) !(Digit n a)
  deriving (Functor, Foldable, Traversable)

data Digit n a
  = One !(Array n a)
  | Two !(Array n a) !(Array n a)
  | Three !(Array n a) !(Array n a) !(Array n a)
  | Four !(Array n a) !(Array n a) !(Array n a) !(Array n a)
  deriving (Functor, Foldable, Traversable)

-- | A representation of a possibly-too-large digit.
data DigitP n a
  = DigP !(Digit n a)
  | FiveP !(Array n a) !(Array n a) !(Array n a) !(Array n a) !(Array n a)

-- | A representation of a possibly-too-small digit.
data DigitM n a
  = ZeroM
  | DigM !(Digit n a)

consDigit :: Array n a -> Digit n a -> DigitP n a
consDigit sa1 (One sa2) = DigP $ Two sa1 sa2
consDigit sa1 (Two sa2 sa3) = DigP $ Three sa1 sa2 sa3
consDigit sa1 (Three sa2 sa3 sa4) = DigP $ Four sa1 sa2 sa3 sa4
consDigit sa1 (Four sa2 sa3 sa4 sa5) = FiveP sa1 sa2 sa3 sa4 sa5
{-# INLINE consDigit #-}

snocDigit :: Digit n a -> Array n a -> DigitP n a
snocDigit (One sa1) sa2 = DigP $ Two sa1 sa2
snocDigit (Two sa1 sa2) sa3 = DigP $ Three sa1 sa2 sa3
snocDigit (Three sa1 sa2 sa3) sa4 = DigP $ Four sa1 sa2 sa3 sa4
snocDigit (Four sa1 sa2 sa3 sa4) sa5 = FiveP sa1 sa2 sa3 sa4 sa5
{-# INLINE snocDigit #-}

consA :: Size n -> Array n a -> Deque n a -> Deque n a
consA !_ sa Empty = Shallow sa
consA !_ sa1 (Shallow sa2) = Deep (One sa1) Empty (One sa2)
consA !n x (Deep pr m sf) = case consDigit x pr of
  DigP pr' -> deepL pr' m sf
  FiveP sa1 sa2 sa3 sa4 sa5 ->
    case sf of
      One ta ->
        case shiftRA (A.twice n) (A.append n sa4 sa5) m of
          ShiftedR m' ga
            | (ta1, ta2) <- A.splitArray n ga
            -> Deep (Three sa1 sa2 sa3) m' (Three ta1 ta2 ta)
      Four ta1 ta2 ta3 ta4 ->
        Deep (Three sa1 sa2 sa3)
             (consSnocA (A.twice n)
                        (A.append n sa4 sa5)
                        m
                        (A.append n ta1 ta2))
             (Two ta3 ta4)
      _ ->
        Deep (Three sa1 sa2 sa3)
             (consA (A.twice n) (A.append n sa4 sa5) m)
             sf

snocA :: Size n -> Deque n a -> Array n a -> Deque n a
snocA !_ Empty sa = Shallow sa
snocA !_ (Shallow sa1) sa2 = Deep (One sa1) Empty (One sa2)
snocA !n (Deep pr m sf) x = case snocDigit sf x of
  DigP sf' -> deepR pr m sf'
  FiveP ta1 ta2 ta3 ta4 ta5 ->
    case pr of
      One sa ->
        case shiftLA (A.twice n) m (A.append n ta1 ta2) of
          ShiftedL ga m'
            | (sa1, sa2) <- A.splitArray n ga
            -> Deep (Three sa sa1 sa2) m' (Three ta3 ta4 ta5)
      Four sa1 sa2 sa3 sa4 ->
        Deep (Two sa1 sa2)
             (consSnocA (A.twice n)
                        (A.append n sa3 sa4)
                        m
                        (A.append n ta1 ta2))
             (Three ta3 ta4 ta5)
      _ ->
        Deep pr
             (snocA (A.twice n) m (A.append n ta1 ta2))
             (Three ta3 ta4 ta5)

data ViewL n a
  = EmptyL
  | ConsL !(Array n a) (Deque n a)

data ViewR n a
  = EmptyR
  | SnocR (Deque n a) !(Array n a)

viewLDigit :: Digit n a -> (Array n a, DigitM n a)
viewLDigit (One a) = (a, ZeroM)
viewLDigit (Two a b) = (a, DigM (One b))
viewLDigit (Three a b c) = (a, DigM (Two b c))
viewLDigit (Four a b c d) = (a, DigM (Three b c d))
{-# INLINE viewLDigit #-}

viewRDigit :: Digit n a -> (DigitM n a, Array n a)
viewRDigit (One a) = (ZeroM, a)
viewRDigit (Two a b) = (DigM (One a), b)
viewRDigit (Three a b c) = (DigM (Two a b), c)
viewRDigit (Four a b c d) = (DigM (Three a b c), d)
{-# INLINE viewRDigit #-}

viewLA :: Size n -> Deque n a -> ViewL n a
viewLA !_ Empty = EmptyL
viewLA !_ (Shallow sa) = ConsL sa Empty
viewLA !n (Deep pr m sf)
  | (sa, pr_) <- viewLDigit pr
  = ConsL sa $ case pr_ of
      DigM pr' -> deepL pr' m sf
      ZeroM -> case sf of
        Two ta1 ta2 -> case viewLA (A.twice n) m of
          EmptyL -> Deep (One ta1) Empty (One ta2)
          ConsL m1 m'
            | (sa1, sa2) <- A.splitArray n m1
            -> Deep (Two sa1 sa2) m' sf
        Three ta1 ta2 ta3 -> case viewLA (A.twice n) m of
          EmptyL -> Deep (Two ta1 ta2) Empty (One ta3)
          ConsL m1 m'
            | (sa1, sa2) <- A.splitArray n m1
            -> Deep (Two sa1 sa2) m' sf
        One ta -> case unconsUnsnocA (A.twice n) m of
          EmptyUCUS -> Shallow ta
          OneUCUS me
            | (m1, m2) <- A.splitArray n me
            -> Deep (Two m1 m2) Empty sf
          UCUS mb m' me
            | (mb1, mb2) <- A.splitArray n mb
            , (me1, me2) <- A.splitArray n me
            -> Deep (Two mb1 mb2) m' (Three me1 me2 ta)
        Four ta1 ta2 ta3 ta4
            | ShiftedL mb m' <- shiftLA (A.twice n) m (A.append n ta1 ta2)
            , (m1, m2) <- A.splitArray n mb
            -> Deep (Two m1 m2) m' (Two ta3 ta4)

viewRA :: Size n -> Deque n a -> ViewR n a
viewRA !_ Empty = EmptyR
viewRA !_ (Shallow sa) = SnocR Empty sa
viewRA !n (Deep pr m sf)
  | (sf_, ta) <- viewRDigit sf
  = flip SnocR ta $ case sf_ of
      DigM sf' -> deepR pr m sf'
      ZeroM -> case pr of
        Two sa1 sa2 -> case viewRA (A.twice n) m of
          EmptyR -> Deep (One sa1) Empty (One sa2)
          SnocR m' m1
            | (ta1, ta2) <- A.splitArray n m1
            -> Deep pr m' (Two ta1 ta2)
{-
        Three ta1 ta2 ta3 -> case viewLA (A.twice n) m of
          EmptyL -> Deep (Two ta1 ta2) Empty (One ta3)
          ConsL m1 m'
            | (sa1, sa2) <- A.splitArray n m1
            -> Deep (Two sa1 sa2) m' sf
        One ta -> case unconsUnsnocA (A.twice n) m of
          EmptyUCUS -> Shallow ta
          OneUCUS me
            | (m1, m2) <- A.splitArray n me
            -> Deep (Two m1 m2) Empty sf
          UCUS mb m' me
            | (mb1, mb2) <- A.splitArray n mb
            , (me1, me2) <- A.splitArray n me
            -> Deep (Two mb1 mb2) m' (Three me1 me2 ta)
        Four ta1 ta2 ta3 ta4
            | ShiftedL mb m' <- shiftLA (A.twice n) m (A.append n ta1 ta2)
            , (m1, m2) <- A.splitArray n mb
            -> Deep (Two m1 m2) m' (Two ta3 ta4)
-}

data ShiftedL n a = ShiftedL !(Array n a) (Deque n a)
data ShiftedR n a = ShiftedR (Deque n a) !(Array n a)

shiftLA :: Size n -> Deque n a -> Array n a -> ShiftedL n a
shiftLA !_ Empty sa = ShiftedL sa Empty
shiftLA !_ (Shallow sa1) sa2 = ShiftedL sa1 (Shallow sa2)
{-
shiftLA !n (Deep pr m sf) sa
  | (x, pr') <- viewLDigit pr
  = ShiftedL x (sa `seq` fixup n pr' m (snocDigit sf sa))
-}

shiftRA :: Size n -> Array n a -> Deque n a -> ShiftedR n a
shiftRA !_ sa Empty = ShiftedR Empty sa
shiftRA !_ sa1 (Shallow sa2) = ShiftedR (Shallow sa1) sa2
{-
shiftRA !n sa (Deep pr m sf)
  | (sf', x) <- viewRDigit sf
  = ShiftedR (sa `seq` fixup n (consDigit sa pr) m sf') x
-}

consSnocA :: Size n -> Array n a -> Deque n a -> Array n a -> Deque n a
consSnocA !_ !sa1 Empty !sa2 = Deep (One sa1) Empty (One sa2)
consSnocA !_ !sa1 (Shallow sa2) !sa3 = Deep (Two sa1 sa2) Empty (One sa3)
{-
consSnocA !n !sa1 (Deep pr m sf) !sa2
  = fixup n (consDigit sa1 pr) m (snocDigit sf sa2)
-}

data UCUS n a
  = EmptyUCUS
  | OneUCUS !(Array n a)
  | UCUS !(Array n a) (Deque n a) !(Array n a)

unconsUnsnocA :: Size n -> Deque n a -> UCUS n a
unconsUnsnocA !_ Empty = EmptyUCUS
unconsUnsnocA !_ (Shallow sa) = OneUCUS sa
{-
unconsUnsnocA !n (Deep pr m sf)
  | (sa1, pr') <- viewLDigit pr
  , (sf', sa2) <- viewRDigit sf
  = UCUS sa1 (fixup n pr' m sf') sa2
-}

-- Put together a Deep node, forcing the middle if it's unsafe.
-- We may end up forcing a middle that we should already know is
-- forced, but that's not a huge deal and it saves considerable
-- code complexity.
deep :: Digit n a -> Deque ('Twice n) a -> Digit n a -> Deque n a
deep pr m sf
  | safe pr && safe sf = Deep pr m sf
  | otherwise = m `seq` Deep pr m sf
{-# INLINE deep #-}

deepL :: Digit n a -> Deque ('Twice n) a -> Digit n a -> Deque n a
deepL pr m sf
  | safe pr = Deep pr m sf
  | otherwise = m `seq` Deep pr m sf
{-# INLINE deepL #-}

deepR :: Digit n a -> Deque ('Twice n) a -> Digit n a -> Deque n a
deepR pr m sf
  | safe sf = Deep pr m sf
  | otherwise = m `seq` Deep pr m sf
{-# INLINE deepR #-}

safe :: Digit n a -> Bool
safe One{} = False
safe Two{} = True
safe Three{} = True
safe Four{} = False
{-# INLINE safe #-}
