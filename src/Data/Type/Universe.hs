{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Data.Type.Universe
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- A type family for "containers", intended for allowing lifting of
-- predicates on @k@ to be predicates on containers @f k@.
module Data.Type.Universe (
  -- * Universe
  Elem,
  In,
  Universe (..),
  singAll,

  -- ** Instances
  Index (..),
  IJust (..),
  IRight (..),
  NEIndex (..),
  ISnd (..),
  IIdentity (..),

  -- ** Predicates
  All,
  WitAll (..),
  NotAll,
  Any,
  WitAny (..),
  None,
  Null,
  NotNull,

  -- *** Specialized
  IsJust,
  IsNothing,
  IsRight,
  IsLeft,

  -- * Decisions and manipulations
  decideAny,
  decideAll,
  genAll,
  igenAll,
  splitSing,
  pickElem,
) where

import Data.Either.Singletons hiding (IsLeft, IsRight)
import Data.Functor.Identity
import Data.Functor.Identity.Singletons
import Data.Kind
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty.Singletons as NE
import Data.List.Singletons hiding (
  All,
  Any,
  Elem,
  ElemSym0,
  ElemSym1,
  ElemSym2,
  Null,
 )
import Data.Maybe.Singletons hiding (IsJust, IsNothing)
import Data.Singletons
import Data.Singletons.Decide
import Data.Tuple.Singletons
import Data.Type.Functor.Product
import Data.Type.Predicate
import Data.Type.Predicate.Logic
import GHC.Generics ((:*:) (..))
import Prelude hiding (all, any)

-- | A @'WitAny' p as@ is a witness that, for at least one item @a@ in the
-- type-level collection @as@, the predicate @p a@ is true.
data WitAny f :: (k ~> Type) -> f k -> Type where
  WitAny :: Elem f as a -> p @@ a -> WitAny f p as

-- | An @'Any' f p@ is a predicate testing a collection @as :: f a@ for the
-- fact that at least one item in @as@ satisfies @p@.  Represents the
-- "exists" quantifier over a given universe.
--
-- This is mostly useful for its 'Decidable' and 'TFunctor' instances,
-- which lets you lift predicates on @p@ to predicates on @'Any' f p@.
data Any f :: Predicate k -> Predicate (f k)

type instance Apply (Any f p) as = WitAny f p as

-- | A @'WitAll' p as@ is a witness that the predicate @p a@ is true for all
-- items @a@ in the type-level collection @as@.
newtype WitAll f p (as :: f k) = WitAll {runWitAll :: forall a. Elem f as a -> p @@ a}

-- | An @'All' f p@ is a predicate testing a collection @as :: f a@ for the
-- fact that /all/ items in @as@ satisfy @p@.  Represents the "forall"
-- quantifier over a given universe.
--
-- This is mostly useful for its 'Decidable', 'Provable', and 'TFunctor'
-- instances, which lets you lift predicates on @p@ to predicates on @'All'
-- f p@.
data All f :: Predicate k -> Predicate (f k)

type instance Apply (All f p) as = WitAll f p as

instance (Universe f, Decidable p) => Decidable (Any f p) where
  decide = decideAny @f @_ @p $ decide @p

instance (Universe f, Decidable p) => Decidable (All f p) where
  decide = decideAll @f @_ @p $ decide @p

instance (Universe f, Provable p) => Decidable (NotNull f ==> Any f p)

instance Provable p => Provable (NotNull f ==> Any f p) where
  prove _ (WitAny i s) = WitAny i (prove @p s)

instance (Universe f, Provable p) => Provable (All f p) where
  prove xs = WitAll $ \i -> prove @p (indexSing i xs)

instance Universe f => TFunctor (Any f) where
  tmap f xs (WitAny i x) = WitAny i (f (indexSing i xs) x)

instance Universe f => TFunctor (All f) where
  tmap f xs a = WitAll $ \i -> f (indexSing i xs) (runWitAll a i)

instance Universe f => DFunctor (All f) where
  dmap f xs a = idecideAll (\i x -> f x (runWitAll a i)) xs

-- | Typeclass for a type-level container that you can quantify or lift
-- type-level predicates over.
class FProd f => Universe (f :: Type -> Type) where
  -- | 'decideAny', but providing an 'Elem'.
  idecideAny ::
    forall k (p :: k ~> Type) (as :: f k).
    () =>
    -- | predicate on value
    (forall a. Elem f as a -> Sing a -> Decision (p @@ a)) ->
    -- | predicate on collection
    (Sing as -> Decision (Any f p @@ as))

  -- | 'decideAll', but providing an 'Elem'.
  idecideAll ::
    forall k (p :: k ~> Type) (as :: f k).
    () =>
    -- | predicate on value
    (forall a. Elem f as a -> Sing a -> Decision (p @@ a)) ->
    -- | predicate on collection
    (Sing as -> Decision (All f p @@ as))

  allProd ::
    forall p g.
    () =>
    (forall a. Sing a -> p @@ a -> g a) ->
    All f p --> TyPred (Prod f g)

  prodAll ::
    forall p g as.
    () =>
    (forall a. g a -> p @@ a) ->
    Prod f g as ->
    All f p @@ as

-- | Predicate that a given @as :: f k@ is empty and has no items in it.
type Null f = (None f Evident :: Predicate (f k))

-- | Predicate that a given @as :: f k@ is not empty, and has at least one
-- item in it.
type NotNull f = (Any f Evident :: Predicate (f k))

-- | A @'None' f p@ is a predicate on a collection @as@ that no @a@ in @as@
-- satisfies predicate @p@.
type None f p = (Not (Any f p) :: Predicate (f k))

-- | A @'NotAll' f p@ is a predicate on a collection @as@ that at least one
-- @a@ in @as@ does not satisfy predicate @p@.
type NotAll f p = (Not (All f p) :: Predicate (f k))

-- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
-- a collection @as@ that is true if and only if /any/ item in @as@
-- satisfies the original predicate.
--
-- That is, it turns a predicate of kind @k ~> Type@ into a predicate
-- of kind @f k ~> Type@.
--
-- Essentially tests existential quantification.
decideAny ::
  forall f k (p :: k ~> Type).
  Universe f =>
  -- | predicate on value
  Decide p ->
  -- | predicate on collection
  Decide (Any f p)
decideAny f = idecideAny (const f)

-- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
-- a collection @as@ that is true if and only if /all/ items in @as@
-- satisfies the original predicate.
--
-- That is, it turns a predicate of kind @k ~> Type@ into a predicate
-- of kind @f k ~> Type@.
--
-- Essentially tests universal quantification.
decideAll ::
  forall f k (p :: k ~> Type).
  Universe f =>
  -- | predicate on value
  Decide p ->
  -- | predicate on collection
  Decide (All f p)
decideAll f = idecideAll (const f)

-- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
splitSing ::
  forall f k (as :: f k).
  Universe f =>
  Sing as ->
  All f (TyPred Sing) @@ as
splitSing = prodAll id . singProd

-- | Automatically generate a witness for a member, if possible
pickElem ::
  forall f k (as :: f k) a.
  (Universe f, SingI as, SingI a, SDecide k) =>
  Decision (Elem f as a)
pickElem =
  mapDecision
    (\case WitAny i Refl -> i)
    (\case i -> WitAny i Refl)
    . decide @(Any f (TyPred ((:~:) a)))
    $ sing

-- | 'genAll', but providing an 'Elem'.
igenAll ::
  forall f k (p :: k ~> Type) (as :: f k).
  Universe f =>
  -- | always-true predicate on value
  (forall a. Elem f as a -> Sing a -> p @@ a) ->
  -- | always-true predicate on collection
  (Sing as -> All f p @@ as)
igenAll f = prodAll (\(i :*: x) -> f i x) . imapProd (:*:) . singProd

-- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- p as@.  Basically witnesses the definition of 'All'.
genAll ::
  forall f k (p :: k ~> Type).
  Universe f =>
  -- | always-true predicate on value
  Prove p ->
  -- | always-true predicate on collection
  Prove (All f p)
genAll f = prodAll f . singProd

-- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
singAll ::
  forall f k (as :: f k).
  Universe f =>
  Sing as ->
  All f Evident @@ as
singAll = prodAll id . singProd

-- | Test that a 'Maybe' is 'Just'.
--
-- @since 0.1.2.0
type IsJust = (NotNull Maybe :: Predicate (Maybe k))

-- | Test that a 'Maybe' is 'Nothing'.
--
-- @since 0.1.2.0
type IsNothing = (Null Maybe :: Predicate (Maybe k))

-- | Test that an 'Either' is 'Right'
--
-- @since 0.1.2.0
type IsRight = (NotNull (Either j) :: Predicate (Either j k))

-- | Test that an 'Either' is 'Left'
--
-- @since 0.1.2.0
type IsLeft = (Null (Either j) :: Predicate (Either j k))

instance Universe [] where
  idecideAny ::
    forall k (p :: k ~> Type) (as :: [k]).
    () =>
    (forall a. Elem [] as a -> Sing a -> Decision (p @@ a)) ->
    Sing as ->
    Decision (Any [] p @@ as)
  idecideAny f = \case
    SNil -> Disproved $ \case
      WitAny i _ -> case i of {}
    x `SCons` xs -> case f IZ x of
      Proved p -> Proved $ WitAny IZ p
      Disproved v -> case idecideAny @[] @_ @p (f . IS) xs of
        Proved (WitAny i p) -> Proved $ WitAny (IS i) p
        Disproved vs -> Disproved $ \case
          WitAny IZ p -> v p
          WitAny (IS i) p -> vs (WitAny i p)

  idecideAll ::
    forall k (p :: k ~> Type) (as :: [k]).
    () =>
    (forall a. Elem [] as a -> Sing a -> Decision (p @@ a)) ->
    Sing as ->
    Decision (All [] p @@ as)
  idecideAll f = \case
    SNil -> Proved $ WitAll $ \case {}
    x `SCons` xs -> case f IZ x of
      Proved p -> case idecideAll @[] @_ @p (f . IS) xs of
        Proved a -> Proved $ WitAll $ \case
          IZ -> p
          IS i -> runWitAll a i
        Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . IS)
      Disproved v -> Disproved $ \a -> v $ runWitAll a IZ

  allProd ::
    forall p g.
    () =>
    (forall a. Sing a -> p @@ a -> g a) ->
    All [] p --> TyPred (Prod [] g)
  allProd f = go
    where
      go :: Sing as -> WitAll [] p as -> Prod [] g as
      go = \case
        SNil -> \_ -> RNil
        x `SCons` xs -> \a ->
          f x (runWitAll a IZ)
            :& go xs (WitAll (runWitAll a . IS))

  prodAll ::
    forall p g as.
    () =>
    (forall a. g a -> p @@ a) ->
    Prod [] g as ->
    All [] p @@ as
  prodAll f = go
    where
      go :: Prod [] g bs -> All [] p @@ bs
      go = \case
        RNil -> WitAll $ \case {}
        x :& xs -> WitAll $ \case
          IZ -> f x
          IS i -> runWitAll (go xs) i

instance Universe Maybe where
  idecideAny f = \case
    SNothing -> Disproved $ \case WitAny i _ -> case i of {}
    SJust x -> case f IJust x of
      Proved p -> Proved $ WitAny IJust p
      Disproved v -> Disproved $ \case
        WitAny IJust p -> v p
  idecideAll f = \case
    SNothing -> Proved $ WitAll $ \case {}
    SJust x -> case f IJust x of
      Proved p -> Proved $ WitAll $ \case IJust -> p
      Disproved v -> Disproved $ \a -> v $ runWitAll a IJust
  allProd f = \case
    SNothing -> \_ -> PNothing
    SJust x -> \a -> PJust (f x (runWitAll a IJust))
  prodAll f = \case
    PNothing -> WitAll $ \case {}
    PJust x -> WitAll $ \case IJust -> f x

instance Universe (Either j) where
  idecideAny f = \case
    SLeft _ -> Disproved $ \case WitAny i _ -> case i of {}
    SRight x -> case f IRight x of
      Proved p -> Proved $ WitAny IRight p
      Disproved v -> Disproved $ \case
        WitAny IRight p -> v p
  idecideAll f = \case
    SLeft _ -> Proved $ WitAll $ \case {}
    SRight x -> case f IRight x of
      Proved p -> Proved $ WitAll $ \case IRight -> p
      Disproved v -> Disproved $ \a -> v $ runWitAll a IRight
  allProd f = \case
    SLeft w -> \_ -> PLeft w
    SRight x -> \a -> PRight (f x (runWitAll a IRight))
  prodAll f = \case
    PLeft _ -> WitAll $ \case {}
    PRight x -> WitAll $ \case IRight -> f x

instance Universe NonEmpty where
  idecideAny ::
    forall k (p :: k ~> Type) (as :: NonEmpty k).
    () =>
    (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a)) ->
    Sing as ->
    Decision (Any NonEmpty p @@ as)
  idecideAny f (x NE.:%| xs) = case f NEHead x of
    Proved p -> Proved $ WitAny NEHead p
    Disproved v -> case idecideAny @[] @_ @p (f . NETail) xs of
      Proved (WitAny i p) -> Proved $ WitAny (NETail i) p
      Disproved vs -> Disproved $ \case
        WitAny i p -> case i of
          NEHead -> v p
          NETail i' -> vs (WitAny i' p)

  idecideAll ::
    forall k (p :: k ~> Type) (as :: NonEmpty k).
    () =>
    (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a)) ->
    Sing as ->
    Decision (All NonEmpty p @@ as)
  idecideAll f (x NE.:%| xs) = case f NEHead x of
    Proved p -> case idecideAll @[] @_ @p (f . NETail) xs of
      Proved ps -> Proved $ WitAll $ \case
        NEHead -> p
        NETail i -> runWitAll ps i
      Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . NETail)
    Disproved v -> Disproved $ \a -> v $ runWitAll a NEHead

  allProd ::
    forall p g.
    () =>
    (forall a. Sing a -> p @@ a -> g a) ->
    All NonEmpty p --> TyPred (Prod NonEmpty g)
  allProd f (x NE.:%| xs) a =
    f x (runWitAll a NEHead)
      :&| allProd @[] @p f xs (WitAll (runWitAll a . NETail))
  prodAll ::
    forall p g as.
    () =>
    (forall a. g a -> p @@ a) ->
    Prod NonEmpty g as ->
    All NonEmpty p @@ as
  prodAll f (x :&| xs) = WitAll $ \case
    NEHead -> f x
    NETail i -> runWitAll (prodAll @[] @p f xs) i

instance Universe ((,) j) where
  idecideAny f (STuple2 _ x) = case f ISnd x of
    Proved p -> Proved $ WitAny ISnd p
    Disproved v -> Disproved $ \case WitAny ISnd p -> v p
  idecideAll f (STuple2 _ x) = case f ISnd x of
    Proved p -> Proved $ WitAll $ \case ISnd -> p
    Disproved v -> Disproved $ \a -> v $ runWitAll a ISnd
  allProd f (STuple2 w x) a = PTup w $ f x (runWitAll a ISnd)
  prodAll f (PTup _ x) = WitAll $ \case ISnd -> f x

-- | The single-pointed universe.
instance Universe Identity where
  idecideAny f (SIdentity x) =
    mapDecision
      (WitAny IId)
      (\case WitAny IId p -> p)
      $ f IId x
  idecideAll f (SIdentity x) =
    mapDecision
      (\p -> WitAll $ \case IId -> p)
      (\y -> runWitAll y IId)
      $ f IId x
  allProd f (SIdentity x) a = PIdentity $ f x (runWitAll a IId)
  prodAll f (PIdentity x) = WitAll $ \case IId -> f x
