{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Predicate.Logic (
    Evident, Impossible
  , type Not, decideNot
  , type (&&&), decideAnd
  , type (|||), decideOr
  , type (^^^), decideXor
  , type (==>), proveImplies
  , explosion, atom, excludedMiddle
  ) where

import           Data.Type.Predicate
import           Data.Singletons
import           Data.Singletons.Decide

-- | @'Not' p@ is the predicate that @p@ is not true.
data Not :: Predicate k -> Predicate k
type instance Apply (Not p) a = Refuted (p @@ a)

instance Decidable p => Decidable (Not p) where
    decide (x :: Sing a) = decideNot @p @a (decide @p x)

-- | Decide @Not p@ based on decisions of @p@.
decideNot
    :: forall p a. ()
    => Decision (p @@ a)
    -> Decision (Not p @@ a)
decideNot = \case
    Proved p    -> Disproved ($ p)
    Disproved v -> Proved v

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

-- | TODO: this might be better stated in terms of some or-constraint.
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

infixr 2 ==>

instance Decidable (Impossible ==> p) where
instance Provable (Impossible ==> p) where
    prove = explosion @p

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

-- | From @'Impossible' @@ a@, you can prove anything.  Essentially
-- a lifted version of 'absurd'.
explosion :: Impossible --> p
explosion _ = \case {}

-- | 'Evident' can be proven from all predicates.
atom :: p --> Evident
atom = const

-- | We cannot have both @p@ and @'Not' p@.
excludedMiddle :: (p &&& Not p) --> Impossible
excludedMiddle _ (p, notP) = notP p
