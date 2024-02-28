{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Data.Type.Predicate.Quantification
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Higher-level predicates for quantifying predicates over universes and
-- sets.
module Data.Type.Predicate.Quantification (
  -- * Any
  Any,
  WitAny (..),
  None,
  anyImpossible,

  -- ** Decision
  decideAny,
  idecideAny,
  decideNone,
  idecideNone,

  -- ** Entailment
  entailAny,
  ientailAny,
  entailAnyF,
  ientailAnyF,

  -- * All
  All,
  WitAll (..),
  NotAll,

  -- ** Decision
  decideAll,
  idecideAll,

  -- ** Entailment
  entailAll,
  ientailAll,
  entailAllF,
  ientailAllF,
  decideEntailAll,
  idecideEntailAll,

  -- * Logical interplay
  allToAny,
  allNotNone,
  noneAllNot,
  anyNotNotAll,
  notAllAnyNot,
) where

import Data.Kind
import Data.Singletons
import Data.Singletons.Decide
import Data.Type.Functor.Product
import Data.Type.Predicate
import Data.Type.Predicate.Logic
import Data.Type.Universe

-- | 'decideNone', but providing an 'Elem'.
idecideNone ::
  forall f k (p :: k ~> Type) (as :: f k).
  Universe f =>
  -- | predicate on value
  (forall a. Elem f as a -> Sing a -> Decision (p @@ a)) ->
  -- | predicate on collection
  (Sing as -> Decision (None f p @@ as))
idecideNone f xs = decideNot @(Any f p) $ idecideAny f xs

-- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
-- a collection @as@ that is true if and only if /no/ item in @as@
-- satisfies the original predicate.
--
-- That is, it turns a predicate of kind @k ~> Type@ into a predicate
-- of kind @f k ~> Type@.
decideNone ::
  forall f k (p :: k ~> Type).
  Universe f =>
  -- | predicate on value
  Decide p ->
  -- | predicate on collection
  Decide (None f p)
decideNone f = idecideNone (const f)

-- | 'entailAny', but providing an 'Elem'.
ientailAny ::
  forall f p q as.
  (Universe f, SingI as) =>
  -- | implication
  (forall a. Elem f as a -> Sing a -> p @@ a -> q @@ a) ->
  Any f p @@ as ->
  Any f q @@ as
ientailAny f (WitAny i x) = WitAny i (f i (indexSing i sing) x)

-- | If there exists an @a@ s.t. @p a@, and if @p@ implies @q@, then there
-- must exist an @a@ s.t. @q a@.
entailAny ::
  forall f p q.
  Universe f =>
  (p --> q) ->
  (Any f p --> Any f q)
entailAny = tmap @(Any f)

-- | 'entailAll', but providing an 'Elem'.
ientailAll ::
  forall f p q as.
  (Universe f, SingI as) =>
  -- | implication
  (forall a. Elem f as a -> Sing a -> p @@ a -> q @@ a) ->
  All f p @@ as ->
  All f q @@ as
ientailAll f a = WitAll $ \i -> f i (indexSing i sing) (runWitAll a i)

-- | If for all @a@ we have @p a@, and if @p@ implies @q@, then for all @a@
-- we must also have @p a@.
entailAll ::
  forall f p q.
  Universe f =>
  (p --> q) ->
  (All f p --> All f q)
entailAll = tmap @(All f)

-- | 'entailAnyF', but providing an 'Elem'.
ientailAnyF ::
  forall f p q as h.
  Functor h =>
  -- | implication in context
  (forall a. Elem f as a -> p @@ a -> h (q @@ a)) ->
  Any f p @@ as ->
  h (Any f q @@ as)
ientailAnyF f = \case WitAny i x -> WitAny i <$> f i x

-- | If @p@ implies @q@ under some context @h@, and if there exists some
-- @a@ such that @p a@, then there must exist some @a@ such that @p q@
-- under that context @h@.
--
-- @h@ might be something like, say, 'Maybe', to give predicate that is
-- either provably true or unprovably false.
--
-- Note that it is not possible to do this with @p a -> 'Decision' (q a)@.
-- This is if the @p a -> 'Decision' (q a)@ implication is false, there
-- it doesn't mean that there is /no/ @a@ such that @q a@, necessarily.
-- There could have been an @a@ where @p@ does not hold, but @q@ does.
entailAnyF ::
  forall f p q h.
  (Universe f, Functor h) =>
  -- | implication in context
  (p --># q) h ->
  (Any f p --># Any f q) h
entailAnyF f x a =
  withSingI x $
    ientailAnyF @f @p @q (\i -> f (indexSing i x)) a

-- | 'entailAllF', but providing an 'Elem'.
ientailAllF ::
  forall f p q as h.
  (Universe f, Applicative h, SingI as) =>
  -- | implication in context
  (forall a. Elem f as a -> p @@ a -> h (q @@ a)) ->
  All f p @@ as ->
  h (All f q @@ as)
ientailAllF f a =
  fmap (prodAll getWit)
    . itraverseProd (\i _ -> Wit @q <$> f i (runWitAll a i))
    $ singProd (sing @as)

-- | If @p@ implies @q@ under some context @h@, and if we have @p a@ for
-- all @a@, then we must have @q a@ for all @a@ under context @h@.
entailAllF ::
  forall f p q h.
  (Universe f, Applicative h) =>
  -- | implication in context
  (p --># q) h ->
  (All f p --># All f q) h
entailAllF f x a =
  withSingI x $
    ientailAllF @f @p @q (\i -> f (indexSing i x)) a

-- | 'entailAllF', but providing an 'Elem'.
idecideEntailAll ::
  forall f p q as.
  (Universe f, SingI as) =>
  -- | decidable implication
  (forall a. Elem f as a -> p @@ a -> Decision (q @@ a)) ->
  All f p @@ as ->
  Decision (All f q @@ as)
idecideEntailAll f a = idecideAll (\i _ -> f i (runWitAll a i)) sing

-- | If we have @p a@ for all @a@, and @p a@ can be used to test for @q a@,
-- then we can test all @a@s for @q a@.
decideEntailAll ::
  forall f p q.
  Universe f =>
  p -?> q ->
  All f p -?> All f q
decideEntailAll = dmap @(All f)

-- | It is impossible for any value in a collection to be 'Impossible'.
--
-- @since 0.1.2.0
anyImpossible :: Universe f => Any f Impossible --> Impossible
anyImpossible _ (WitAny i p) = p . indexSing i

-- | If any @a@ in @as@ does not satisfy @p@, then not all @a@ in @as@
-- satisfy @p@.
--
-- @since 0.1.2.0
anyNotNotAll :: Any f (Not p) --> NotAll f p
anyNotNotAll _ (WitAny i v) a = v $ runWitAll a i

-- | If not all @a@ in @as@ satisfy @p@, then there must be at least one
-- @a@ in @as@ that does not satisfy @p@.  Requires @'Decidable' p@ in
-- order to locate that specific @a@.
--
-- @since 0.1.2.0
notAllAnyNot ::
  forall f p.
  (Universe f, Decidable p) =>
  NotAll f p --> Any f (Not p)
notAllAnyNot xs vAll = elimDisproof (decide @(Any f (Not p)) xs) $ \vAny ->
  vAll $ WitAll $ \i ->
    elimDisproof (decide @p (indexSing i xs)) $ \vP ->
      vAny $ WitAny i vP

-- | If @p@ is false for all @a@ in @as@, then no @a@ in @as@ satisfies
-- @p@.
--
-- @since 0.1.2.0
allNotNone :: All f (Not p) --> None f p
allNotNone _ a (WitAny i v) = runWitAll a i v

-- | If no @a@ in @as@ satisfies @p@, then @p@ is false for all @a@ in
-- @as@.  Requires @'Decidable' p@ to interrogate the input disproof.
--
-- @since 0.1.2.0
noneAllNot ::
  forall f p.
  (Universe f, Decidable p) =>
  None f p --> All f (Not p)
noneAllNot xs vAny = elimDisproof (decide @(All f (Not p)) xs) $ \vAll ->
  vAll $ WitAll $ \i p -> vAny $ WitAny i p

-- | If something is true for all xs, then it must be true for at least one
-- x in xs, provided that xs is not empty.
--
-- @since 0.1.5.0
allToAny :: (All f p &&& NotNull f) --> Any f p
allToAny _ (a, WitAny i _) = WitAny i $ runWitAll a i
