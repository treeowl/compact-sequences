{-# language CPP #-}
{-# language BangPatterns, ScopedTypeVariables, UnboxedTuples, MagicHash #-}
{-# language DeriveTraversable, StandaloneDeriving #-}
{-# language DataKinds #-}
-- {-# OPTIONS_GHC -Wall #-}

module Data.CompactSequence.Queue.Internal where
--import Data.Primitive.SmallArray (SmallArray)
--import qualified Data.Primitive.SmallArray as A
import qualified Data.CompactSequence.Internal.Array as A
import Data.CompactSequence.Internal.Array (Array, Size, Mult (..))
import qualified Data.Foldable as F
import Data.Function (on)

data FD n a
  = FD1 !(Array n a)
  | FD2 !(Array n a) !(Array n a)
  | FD3 !(Array n a) !(Array n a) !(Array n a)
  deriving (Functor, Foldable, Traversable)
-- FD2 and FD3 are safe; FD1 is dangerous.

data RD n a
  = RD0
  | RD1 !(Array n a)
  | RD2 !(Array n a) !(Array n a)
  deriving (Functor, Foldable, Traversable)
-- RD0 and RD1 are safe; RD2 is dangerous.

data Queue n a
  = Empty
  | Node !(FD n a) (Queue ('Twice n) a) !(RD n a)
  deriving (Functor, Traversable)
-- An Empty node is safe.
-- A Node node is safe if both its digits are safe. We require that the child queue of an unsafe
-- node be in WHNF, and allow no debits on it.
--
--
-- To calculate the debit allowance of the child queue of a *safe* node:
--
-- To each ancestor of the node, assign 1 if the node is safe and 0 if it is
-- unsafe. Calculate the value of the binary number so obtained. For example,
-- given
--
-- Safe
-- Safe
-- Dangerous
-- Safe
-- Node
--
-- the *safety value* above Node, sv(Node), is 1*1+1*2+0*4+1*8 = 11
--
-- We allow the child queue of a safe node four times its safety value (for some value of four).

data ViewA n a
  = EmptyA
  | ConsA !(Array n a) (Queue n a)

data ViewA2 n a
  = EmptyA2
  | ConsA2 !(Array n a) !(Array n a) (Queue n a)

singletonA :: Array n a -> Queue n a
singletonA sa = Node (FD1 sa) Empty RD0

viewA :: Size n -> Queue n a -> ViewA n a
-- Non-cascading
viewA !_ Empty = EmptyA
viewA !_ (Node (FD3 sa1 sa2 sa3) m sf) = ConsA sa1 $ Node (FD2 sa2 sa3) m sf
viewA !_ (Node (FD2 sa1 sa2) m sf) = ConsA sa1 $ m `seq` Node (FD1 sa2) m sf
-- Potentially cascading
viewA !n (Node (FD1 sa1) m (RD2 sa2 sa3)) = ConsA sa1 $
  case shiftA (A.twice n) m (A.append n sa2 sa3) of
    ShiftedA sam m'
      | (sam1, sam2) <- A.splitArray n sam
      -> Node (FD2 sam1 sam2) m' RD0
viewA !n (Node (FD1 sa1) m sf) = ConsA sa1 $
  case viewA (A.twice n) m of
    EmptyA -> case sf of
      RD2 sa2 sa3 -> Node (FD2 sa2 sa3) Empty RD0
      RD1 sa2 -> singletonA sa2
      RD0 -> Empty
    ConsA sam m'
      | (sam1, sam2) <- A.splitArray n sam
      -> Node (FD2 sam1 sam2) m' sf

{-
viewA2 :: Size n -> Queue n a -> ViewA2 n a
viewA2 n q = case viewA n q of
  EmptyA -> EmptyA2
  ConsA sa q'
    | (sa1, sa2) <- A.splitArray n sa
    -> ConsA2 sa1 sa2 q'
-}

empty :: Queue n a
empty = Empty


{-
We have some number of unsafe nodes followed by a safe node. Any operation that cascades
will turn any node it passes into a safe one. Let's first see how debit allowances change.
Initially, the prefix contributes no debit allowance. If the last node that changes was
a safe one and it becomes unsafe, that reduces the debit allowance below it. All but
a logarithmic amount of that reduction is offset by the changes from unsafe to safe
nodes above.

For each unsafe node, we may perform `s` splitting work and perform or suspend
`s` appending work. For purposes of amortized analysis, we can pretend that we
perform all of these eagerly. 
-}


snocA :: Size n -> Queue n a -> Array n a -> Queue n a
snocA !_ Empty sa = Node (FD1 sa) empty RD0
snocA !_ (Node pr m RD0) sa = Node pr m (RD1 sa)
snocA !_ (Node pr m (RD1 sa1)) sa2 = m `seq` Node pr m (RD2 sa1 sa2)
snocA !n (Node (FD1 sa0) m (RD2 sa1 sa2)) sa3
  | ShiftedA sam m' <- shiftA (A.twice n) m (A.append n sa1 sa2)
  , (sam1, sam2) <- A.splitArray n sam
  = Node (FD3 sa0 sam1 sam2) m' (RD1 sa3)
snocA !n (Node pr m (RD2 sa1 sa2)) sa3
  = Node pr (snocA (A.twice n) m (A.append n sa1 sa2)) (RD1 sa3)

-- | Uncons from a node and snoc onto it. Ensure that if the operation is
-- expensive then it leaves the node in a safe configuration. Why do we need
-- this? Suppose we have
--
-- Two m Two
--
-- If we snoc onto this, the operation cascades, and we get
--
-- Two m Zero
--
-- Then when we view, we get
--
-- One m Zero
--
-- which is not safe.
--
-- Instead, we need to view first, getting
--
-- One m Two
--
-- immediately, then snoc on, cascading and getting
--
-- Three m Zero
--
-- which is safe.
--
-- If instead we have
--
-- One m One
--
-- we have to do the opposite: snoc then view. We might as well
-- just write a dedicated shifting operation.
shiftA :: Size n -> Queue n a -> Array n a -> ShiftedA n a
-- Non-cascading cases
shiftA !_ Empty sa = ShiftedA sa Empty
shiftA !_ (Node (FD2 sa1 sa2) m RD0) sa3
  = ShiftedA sa1 $ m `seq` Node (FD1 sa2) m (RD1 sa3)
shiftA !_ (Node (FD2 sa1 sa2) m (RD1 sa3)) sa4
  = ShiftedA sa1 $ m `seq` Node (FD1 sa2) m (RD2 sa3 sa4)
shiftA !_ (Node (FD3 sa1 sa2 sa3) m RD0) sa4
  = ShiftedA sa1 $ Node (FD2 sa2 sa3) m (RD1 sa4)
shiftA !_ (Node (FD3 sa1 sa2 sa3) m (RD1 sa4)) sa5
  = ShiftedA sa1 $ m `seq` Node (FD2 sa2 sa3) m (RD2 sa4 sa5)
-- cascading cases
shiftA !n (Node (FD1 sa1) m RD0) sa3
  = ShiftedA sa1 $
      case viewA (A.twice n) m of
        EmptyA -> singletonA sa3
        ConsA sam m'
          | (sam1, sam2) <- A.splitArray n sam
          -> Node (FD2 sam1 sam2) m' (RD1 sa3)
shiftA !n (Node (FD1 sa1) m (RD1 sa2)) sa3
    -- We force sa3 here to avoid forming a chain of thunks if
    -- we have a bunch of FD1+RD1 nodes in a row.
  = ShiftedA sa1 $ sa3 `seq`
      case shiftA (A.twice n) m (A.append n sa2 sa3) of
        ShiftedA sam m'
          | (sam1, sam2) <- A.splitArray n sam
          -> Node (FD2 sam1 sam2) m' RD0
shiftA n (Node (FD1 sa1) m (RD2 sa2 sa3)) sa4
  = ShiftedA sa1 $
      case shiftA (A.twice n) m (A.append n sa2 sa3) of
        ShiftedA sam m'
          | (sam1, sam2) <- A.splitArray n sam
          -> Node (FD2 sam1 sam2) m' (RD1 sa4)
shiftA n (Node (FD2 sa1 sa2) m (RD2 sa3 sa4)) sa5
  = ShiftedA sa1 $
      case shiftA (A.twice n) m (A.append n sa3 sa4) of
        ShiftedA sam m'
          | (sam1, sam2) <- A.splitArray n sam
          -> Node (FD3 sa2 sam1 sam2) m' (RD1 sa5)
shiftA n (Node (FD3 sa1 sa2 sa3) m (RD2 sa4 sa5)) sa6
  = ShiftedA sa1 $ Node (FD2 sa2 sa3) (snocA (A.twice n) m (A.append n sa4 sa5)) (RD1 sa6)

data ShiftedA n a = ShiftedA !(Array n a) (Queue n a)

{-
splitArray :: SmallArray a -> (SmallArray a, SmallArray a)
splitArray sa1 = (sa2, sa3)
  where
    !len' = A.sizeofSmallArray sa1 `quot` 2
    !sa2 = A.cloneSmallArray sa1 0 len'
    !sa3 = A.cloneSmallArray sa1 len' len'
-}

instance Show a => Show (Queue n a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

instance Eq a => Eq (Queue n a) where
  (==) = (==) `on` F.toList

instance Ord a => Ord (Queue n a) where
  compare = compare `on` F.toList

instance Foldable (Queue n) where
  foldMap _f Empty = mempty
  foldMap f (Node pr m sf) = foldMap f pr <> foldMap f m <> foldMap f sf

  null Empty = True
  null _ = False

  -- TODO: Once the size type has really stabilized,
  -- we should find a way to write a custom length.
  -- Until then, we leave that to the wrapper implementation.
