{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.Predicate.Logic
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Logical and algebraic connectives for predicates, as well as common
-- logical combinators.

module Data.Type.Predicate.Logic (
  -- * Top and bottom
    Evident, Impossible
  -- * Logical connectives
  , type Not, decideNot
  , type (&&&), decideAnd
  , type (|||), decideOr
  , type (^^^), decideXor
  , type (==>), proveImplies, Implies
  , type (<==>), Equiv
  -- * Logical deductions
  , compImpl, explosion, atom, excludedMiddle, doubleNegation
  , contrapositive, contrapositive'
  -- ** Lattice
  , projAndFst, projAndSnd, injOrLeft, injOrRight
  ) where

import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude.Bool (Sing(..))
import           Data.Type.Predicate
import           Data.Void

-- | @p '&&&' q@ is a predicate that both @p@ and @q@ are true.
data (&&&) :: Predicate k -> Predicate k -> Predicate k
type instance Apply (p &&& q) a = (p @@ a, q @@ a)
infixr 3 &&&

instance (Decidable p, Decidable q) => Decidable (p &&& q) where
    decide (x :: Sing a) = decideAnd @p @q @a (decide @p x) (decide @q x)

instance (Provable p, Provable q) => Provable (p &&& q) where
    prove x = (prove @p x, prove @q x)

-- | Decide @p '&&&' q@ based on decisions of @p@ and @q@.
decideAnd
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p &&& q) @@ a)
decideAnd = \case
    Proved p    -> \case
      Proved q    -> Proved (p, q)
      Disproved v -> Disproved $ \(_, q) -> v q
    Disproved v -> \_ -> Disproved $ \(p, _) -> v p

-- | @p '|||' q@ is a predicate that either @p@ and @q@ are true.
data (|||) :: Predicate k -> Predicate k -> Predicate k
type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)
infixr 2 |||

instance (Decidable p, Decidable q) => Decidable (p ||| q) where
    decide (x :: Sing a) = decideOr @p @q @a (decide @p x) (decide @q x)

-- | Picks the proof of @p@.  Note that this is instance has stronger
-- constraints than is strictly necessary; we should really only have to
-- require that either @p@ or @q@ is true.
instance (Provable p, Provable q) => Provable (p ||| q) where
    prove x = Left (prove @p x)

-- | Decide @p '|||' q@ based on decisions of @p@ and @q@.
decideOr
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p ||| q) @@ a)
decideOr = \case
    Proved p    -> \_ -> Proved $ Left p
    Disproved v -> \case
      Proved q    -> Proved $ Right q
      Disproved w -> Disproved $ \case
        Left p  -> v p
        Right q -> w q

-- | @p '^^^' q@ is a predicate that either @p@ and @q@ are true, but not
-- both.
type p ^^^ q = (p &&& Not q) ||| (Not p &&& q)

-- | Decide @p '^^^' q@ based on decisions of @p@ and @q@.
decideXor
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p ^^^ q) @@ a)
decideXor p q = decideOr @(p &&& Not q) @(Not p &&& q) @a
                  (decideAnd @p @(Not q) @a p (decideNot @q @a q))
                  (decideAnd @(Not p) @q @a (decideNot @p @a p) q)

-- | @p ==> q@ is true if @q@ is provably true under the condition that @p@
-- is true.
data (==>) :: Predicate k -> Predicate k -> Predicate k
type instance Apply (p ==> q) a = p @@ a -> q @@ a

infixr 1 ==>

instance Decidable (Impossible ==> p) where
instance Provable (Impossible ==> p) where
    prove = explosion @p

instance (Decidable (p ==> q), Decidable q) => Decidable (Not q ==> Not p) where
    decide x = case decide @(p ==> q) x of
      Proved pq     -> Proved $ \vq p -> vq (pq p)
      Disproved vpq -> case decide @q x of
        Proved    q  -> Disproved $ \_     -> vpq (const q)
        Disproved vq -> Disproved $ \vnpnq -> vpq (absurd . vnpnq vq)
instance Provable (p ==> q) => Provable (Not q ==> Not p) where
    prove = contrapositive @p @q (prove @(p ==> q))

-- | @'Implies' p q@ is a constraint that @p '==>' q@ is 'Provable'; that
-- is, you can prove that @p@ implies @q@.
type Implies  p q = Provable  (p ==> q)

-- | @'Equiv' p q@ is a constraint that @p '<==>' q@ is 'Provable'; that
-- is, you can prove that @p@ is logically equivalent to @q@.
type Equiv  p q = Provable  (p <==> q)

-- | If @q@ is provable, then so is @p '==>' q@.
--
-- This can be used as an easy plug-in 'Provable' instance for @p '==>' q@
-- if @q@ is 'Provable':
--
-- @
-- instance Provable (p ==> MyPred) where
--     prove = proveImplies @MyPred
-- @
--
-- This instance isn't provided polymorphically because of overlapping
-- instance issues.
proveImplies :: Prove q -> Prove (p ==> q)
proveImplies q x _ = q x

-- | Two-way implication, or logical equivalence
type (p <==> q) = p ==> q &&& q ==> p
infixr 1 <==>

-- | From @'Impossible' @@ a@, you can prove anything.  Essentially
-- a lifted version of 'absurd'.
explosion :: Impossible --> p
explosion x v = absurd $ v x

-- | 'Evident' can be proven from all predicates.
atom :: p --> Evident
atom = const

-- | We cannot have both @p@ and @'Not' p@.
excludedMiddle :: (p &&& Not p) --> Impossible
excludedMiddle _ (p, notP) _ = notP p

-- | If only this worked, but darn overlapping instances.  Same for p ==>
-- p ||| q and p &&& q ==> p :(
-- q) ==>
-- instance Provable (p &&& Not p ==> Impossible) where
--     prove = excludedMiddle @p

-- | If p implies q, then not q implies not p.
contrapositive
    :: (p --> q)
    -> (Not q --> Not p)
contrapositive f x v p = v (f x p)

-- | Reverse direction of 'contrapositive'.  Only possible if @q@ is
-- 'Decidable' on its own, without the help of @p@, which makes this much
-- less useful.
contrapositive'
    :: forall p q. Decidable q
    => (Not q --> Not p)
    -> (p --> q)
contrapositive' f x p = case decide @q x of
    Proved     q -> q
    Disproved vq -> absurd $ f x vq p

-- | Logical double negation.  Only possible if @p@ is 'Decidable'.
doubleNegation :: forall p. Decidable p => Not (Not p) --> p
doubleNegation x vvp = case decide @p x of
    Proved    p  -> p
    Disproved vp -> absurd $ vvp vp

projAndFst :: (p &&& q) --> p
projAndFst _ = fst

projAndSnd :: (p &&& q) --> q
projAndSnd _ = snd

injOrLeft :: forall p q. p --> (p ||| q)
injOrLeft _ = Left

injOrRight :: forall p q. q --> (p ||| q)
injOrRight _ = Right
