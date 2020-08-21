{-# language CPP #-}
{-# language BangPatterns, ScopedTypeVariables, UnboxedTuples, MagicHash #-}
{-# language DeriveTraversable, StandaloneDeriving #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language LambdaCase #-}
{- OPTIONS_GHC -Wall #-}
{- OPTIONS_GHC -ddump-simpl #-}

module Data.CompactSequence.Queue.Internal where
import qualified Data.CompactSequence.Internal.Array as A
import Data.CompactSequence.Internal.Array (Array)
import qualified Data.CompactSequence.Internal.Size as Sz
import Data.CompactSequence.Internal.Size (Size, Twice)
import qualified Data.Foldable as F
import Data.Function (on)

data FD n a
  = FD1 !(Array n a)
  | FD2 !(Array n a) !(Array n a)
  | FD3 !(Array n a) !(Array n a) !(Array n a)
-- FD2 and FD3 are safe; FD1 is dangerous.

data RD n a
  = RD0
  | RD1 !(Array n a)
  | RD2 !(Array n a) !(Array n a)
-- RD0 and RD1 are safe; RD2 is dangerous.

-- Conceptually, we want something like
--
--   data Queue n a = Empty | Node !(FD n a) (Queue n a) !(RD n a)
--
-- Unfortunately, this is rather wasteful. The Node itself takes
-- 4 words, and the digits combined take between 2 and 7. Total:
-- between 6 and 11 words. By manually "unpacking" the digits, expanding
-- the Queue to 10 constructors, we now have nodes taking
-- between 3 and 7 words, a considerable improvement. This kind of
-- unpacking, in general, can risk a loss of sharing, leading to
-- increased allocation and (in the presence of persistence) increased
-- residency. But that doesn't happen here! The worst case for the
-- unpacked representation relative to the conceptual one is when
-- the frost digit is 3 and we modify the rear digit. In that case,
-- we have to copy the three front array pointers rather than a single
-- front digit pointer. Consider, for example, changing a 0 digit
-- to a 1 digit in the rear. For the conceptual representation, that
-- allocates 4 words for the new Node plus 2 words for the new rear
-- digit, for a total of 6 words. The unpacked representation
-- allocates one word for the new node header, three words to copy the
-- front, one word to copy the middle, and one word for the new rear.
-- Total: 6. So in the case that's *worst* for the unpacked version,
-- the unpacked version still breaks even in allocation, while
-- winning the indirection game. So unpacked is the way to go.
-- As long as we're doing it this way, we can bake the "no debits
-- on children of unsafe nodes" invariant right into the constructors,
-- preventing us from messing that up and as a side benefit avoiding
-- some double forcing.

data Queue n a
  = Empty
  | Node10 !(Array n a) !(Queue (Twice n) a)
  | Node11 !(Array n a) !(Queue (Twice n) a) !(Array n a)
  | Node12 !(Array n a) !(Queue (Twice n) a) !(Array n a) !(Array n a)
  | Node20 !(Array n a) !(Array n a) (Queue (Twice n) a)
  | Node21 !(Array n a) !(Array n a) (Queue (Twice n) a) !(Array n a)
  | Node22 !(Array n a) !(Array n a) !(Queue (Twice n) a) !(Array n a) !(Array n a)
  | Node30 !(Array n a) !(Array n a) !(Array n a) (Queue (Twice n) a)
  | Node31 !(Array n a) !(Array n a) !(Array n a) (Queue (Twice n) a) !(Array n a)
  | Node32 !(Array n a) !(Array n a) !(Array n a) !(Queue (Twice n) a) !(Array n a) !(Array n a)
  deriving (Functor, Foldable, Traversable)
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



-- Gunk to define a `Node` pattern synonym to pretend we
-- have real digits. Sadly, where we really want this most,
-- it throws GHC's optimizer for a loop and it makes garbage
-- code.
data Queue_ n a
  = Empty_
  | Node_ !(FD n a) (Queue (Twice n) a) !(RD n a)

matchNode :: Queue n a -> Queue_ n a
matchNode q = case q of
  Empty -> Empty_
  Node10 x m -> Node_ (FD1 x) m RD0
  Node11 x m a -> Node_ (FD1 x) m (RD1 a)
  Node12 x m a b -> Node_ (FD1 x) m (RD2 a b)
  Node20 x y m -> Node_ (FD2 x y) m RD0
  Node21 x y m a -> Node_ (FD2 x y) m (RD1 a)
  Node22 x y m a b -> Node_ (FD2 x y) m (RD2 a b)
  Node30 x y z m -> Node_ (FD3 x y z) m RD0
  Node31 x y z m a -> Node_ (FD3 x y z) m (RD1 a)
  Node32 x y z m a b -> Node_ (FD3 x y z) m (RD2 a b)
{-# INLINE matchNode #-}

pattern Node :: FD n a -> Queue (Twice n) a -> RD n a -> Queue n a
pattern Node pr m sf <- (matchNode -> Node_ pr m sf)
  where
    Node (FD1 x) m RD0 = Node10 x m
    Node (FD1 x) m (RD1 a) = Node11 x m a
    Node (FD1 x) m (RD2 a b) = Node12 x m a b
    Node (FD2 x y) m RD0 = Node20 x y m
    Node (FD2 x y) m (RD1 a) = Node21 x y m a
    Node (FD2 x y) m (RD2 a b) = Node22 x y m a b
    Node (FD3 x y z) m RD0 = Node30 x y z m
    Node (FD3 x y z) m (RD1 a) = Node31 x y z m a
    Node (FD3 x y z) m (RD2 a b) = Node32 x y z m a b

{-# COMPLETE Empty, Node #-}

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
viewA !_ (Node (FD2 sa1 sa2) m sf) = ConsA sa1 $ Node (FD1 sa2) m sf
-- Potentially cascading
viewA !n (Node (FD1 sa1) m (RD2 sa2 sa3)) = ConsA sa1 $
  case shiftA n m sa2 sa3 of
    ShiftedA sam1 sam2 m'
      -> Node (FD2 sam1 sam2) m' RD0
viewA !n (Node (FD1 sa1) m sf) = ConsA sa1 $
  case viewA (Sz.twice n) m of
    EmptyA -> case sf of
      RD2 sa2 sa3 -> Node (FD2 sa2 sa3) Empty RD0
      RD1 sa2 -> singletonA sa2
      RD0 -> Empty
    ConsA sam m'
      | (sam1, sam2) <- A.splitArray n sam
      -> Node (FD2 sam1 sam2) m' sf

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
snocA !n (Node (FD1 sa0) m (RD2 sa1 sa2)) sa3
  | ShiftedA sam1 sam2 m' <- shiftA n m sa1 sa2
  = Node (FD3 sa0 sam1 sam2) m' (RD1 sa3)
snocA !_ (Node pr m RD0) sa = Node pr m (RD1 sa)
snocA !_ (Node pr m (RD1 sa1)) sa2 = Node pr m (RD2 sa1 sa2)
snocA !n (Node pr m (RD2 sa1 sa2)) sa3
  = Node pr (snocA (Sz.twice n) m (A.append n sa1 sa2)) (RD1 sa3)


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
shiftA :: Size n -> Queue (Twice n) a -> Array n a -> Array n a -> ShiftedA n a

-- BLAST AND DARN. I started out using the Node pattern synonym all
-- through here. Sadly, GHC was *way* too eager with join point
-- transformations and decided to actually pass around front
-- and rear digits to make things slow. GRRR. So in this function,
-- we use the raw constructors by hand.

-- Non-cascading cases
shiftA !_ Empty !sa1 !sa2 = ShiftedA sa1 sa2 Empty
shiftA !n (Node20 sa1 sa2 m) !sa3 !sa4
  = shrift n sa1 $ Node11 sa2 m (A.append n sa3 sa4)
shiftA !n (Node21 sa1 sa2 m  sa3) !sa4 !sa5
  = shrift n sa1 $ Node12 sa2 m sa3 (A.append n sa4 sa5)
shiftA !n (Node30 sa1 sa2 sa3 m) !sa4 !sa5
  = shrift n sa1 $ Node21 sa2 sa3 m (A.append n sa4 sa5)
shiftA !n (Node31 sa1 sa2 sa3 m sa4) !sa5 !sa6
  = shrift n sa1 $ Node22 sa2 sa3 m sa4 (A.append n sa5 sa6)
-- cascading cases
shiftA !n (Node10 sa1 m) !sa3 !sa4
  = shrift n sa1 $
      case viewA (Sz.twice (Sz.twice n)) m of
        EmptyA -> Node10 (A.append n sa3 sa4) Empty
        ConsA sam m'
          | (sam1, sam2) <- A.splitArray (Sz.twice n) sam
          -> Node21 sam1 sam2 m' (A.append n sa3 sa4)
shiftA !n (Node11 sa1 m sa2) !sa3 !sa4
  = shrift n sa1 $
      case shiftA (Sz.twice n) m sa2 (A.append n sa3 sa4) of
        ShiftedA sam1 sam2 m'
          -> Node20 sam1 sam2 m'
shiftA n (Node12 sa1 m sa2 sa3) !sa4 !sa5
  = shrift n sa1 $
      case shiftA (Sz.twice n) m sa2 sa3 of
        ShiftedA sam1 sam2 m'
          -> Node21 sam1 sam2 m' (A.append n sa4 sa5)
shiftA n (Node22 sa1 sa2 m sa3 sa4) !sa5 !sa6
  = shrift n sa1 $
      case shiftA (Sz.twice n) m sa3 sa4 of
        ShiftedA sam1 sam2 m'
          -> Node31 sa2 sam1 sam2 m' (A.append n sa5 sa6)
shiftA n (Node32 sa1 sa2 sa3 m sa4 sa5) !sa6 !sa7
  = shrift n sa1 $
      Node21 sa2 sa3
           (snocA (Sz.twice (Sz.twice n)) m (A.append (Sz.twice n) sa4 sa5))
           (A.append n sa6 sa7)

shrift :: Size n -> Array (Twice n) a -> Queue (Twice n) a -> ShiftedA n a
shrift n sa q
  | (sa1, sa2) <- A.splitArray n sa
  = ShiftedA sa1 sa2 q

data ShiftedA n a = ShiftedA !(Array n a) !(Array n a) (Queue (Twice n) a)

instance Show a => Show (Queue n a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (F.toList xs)

instance Eq a => Eq (Queue n a) where
  (==) = (==) `on` F.toList

instance Ord a => Ord (Queue n a) where
  compare = compare `on` F.toList
