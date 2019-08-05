{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

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
--
module Data.Type.Universe (
  -- * Universe
    Elem, In, Universe(..), singAll
  -- ** Instances
  , Index(..), IJust(..), IRight(..), NEIndex(..), ISnd(..), IProxy, IIdentity(..)
  , CompElem(..), SumElem(..)
  , sameIndexVal, sameNEIndexVal
  -- ** Predicates
  , All, WitAll(..), NotAll
  , Any, WitAny(..), None
  , Null, NotNull
  -- *** Specialized
  , IsJust, IsNothing, IsRight, IsLeft
  -- * Decisions and manipulations
  , decideAny, decideAll
  , genAll, igenAll
  , foldMapUni, ifoldMapUni, index, pickElem
  -- * Universe Combination
  -- ** Universe Composition
  , (:.:)(..), sGetComp, GetComp
  , allComp, compAll, anyComp, compAny
  -- ** Universe Disjunction
  , (:+:)(..)
  , anySumL, anySumR, sumLAny, sumRAny
  , allSumL, allSumR, sumLAll, sumRAll
  -- * Defunctionalization symbols
  , ElemSym0, ElemSym1, ElemSym2
  , ProdSym0, ProdSym1, ProdSym2
  , GetCompSym0, GetCompSym1
  -- * Singletons
  , SIndex(..), SIJust(..), SIRight(..), SNEIndex(..), SISnd(..), SIProxy, SIIdentity(..)
  , Sing (SComp, SInL, SIndex', SIJust', SIRight', SNEIndex', SISnd', SIProxy', SIIdentity')
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Predicate
import           Data.Type.Universe.Internal
import           Data.Type.Universe.Prod
import           GHC.Generics                ((:*:)(..))
import           Prelude hiding              (any, all)

---- | A @'WitAny' p as@ is a witness that, for at least one item @a@ in the
---- type-level collection @as@, the predicate @p a@ is true.
--data WitAny f :: (k ~> Type) -> f k -> Type where
--    WitAny :: Elem f as a -> p @@ a -> WitAny f p as

---- | An @'Any' f p@ is a predicate testing a collection @as :: f a@ for the
---- fact that at least one item in @as@ satisfies @p@.  Represents the
---- "exists" quantifier over a given universe.
----
---- This is mostly useful for its 'Decidable' and 'TFunctor' instances,
---- which lets you lift predicates on @p@ to predicates on @'Any' f p@.
--data Any f :: Predicate k -> Predicate (f k)
--type instance Apply (Any f p) as = WitAny f p as

---- | A @'WitAll' p as@ is a witness that the predicate @p a@ is true for all
---- items @a@ in the type-level collection @as@.
--newtype WitAll f p (as :: f k) = WitAll { runWitAll :: forall a. Elem f as a -> p @@ a }

---- | An @'All' f p@ is a predicate testing a collection @as :: f a@ for the
---- fact that /all/ items in @as@ satisfy @p@.  Represents the "forall"
---- quantifier over a given universe.
----
---- This is mostly useful for its 'Decidable', 'Provable', and 'TFunctor'
---- instances, which lets you lift predicates on @p@ to predicates on @'All'
---- f p@.
--data All f :: Predicate k -> Predicate (f k)
--type instance Apply (All f p) as = WitAll f p as

--instance (Universe f, Decidable p) => Decidable (Any f p) where
--    decide = decideAny @f @_ @p $ decide @p

--instance (Universe f, Decidable p) => Decidable (All f p) where
--    decide = decideAll @f @_ @p $ decide @p

--instance (Universe f, Provable p) => Decidable (NotNull f ==> Any f p) where

--instance Provable p => Provable (NotNull f ==> Any f p) where
--    prove _ (WitAny i s) = WitAny i (prove @p s)

--instance (Universe f, Provable p) => Provable (All f p) where
--    prove xs = WitAll $ \i -> prove @p (index i xs)

--instance Universe f => TFunctor (Any f) where
--    tmap f xs (WitAny i x) = WitAny i (f (index i xs) x)

--instance Universe f => TFunctor (All f) where
--    tmap f xs a = WitAll $ \i -> f (index i xs) (runWitAll a i)

--instance Universe f => DFunctor (All f) where
--    dmap f xs a = idecideAll (\i x -> f x (runWitAll a i)) xs

---- | Typeclass for a type-level container that you can quantify or lift
---- type-level predicates over.
--class HasProd f => Universe (f :: Type -> Type) where
--    -- | 'decideAny', but providing an 'Elem'.
--    idecideAny
--        :: forall k (p :: k ~> Type) (as :: f k). ()
--        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
--        -> (Sing as -> Decision (Any f p @@ as))                         -- ^ predicate on collection

--    -- | 'decideAll', but providing an 'Elem'.
--    idecideAll
--        :: forall k (p :: k ~> Type) (as :: f k). ()
--        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
--        -> (Sing as -> Decision (All f p @@ as))                         -- ^ predicate on collection

--    allProd
--        :: forall p g. ()
--        => (forall a. Sing a -> p @@ a -> g a)
--        -> All f p --> TyPred (Prod f g)
--    prodAll
--        :: forall p g as. ()
--        => (forall a. g a -> p @@ a)
--        -> Prod f g as
--        -> All f p @@ as

---- | Predicate that a given @as :: f k@ is empty and has no items in it.
--type Null    f = (None f Evident :: Predicate (f k))

---- | Predicate that a given @as :: f k@ is not empty, and has at least one
---- item in it.
--type NotNull f = (Any f Evident :: Predicate (f k))

---- | A @'None' f p@ is a predicate on a collection @as@ that no @a@ in @as@
---- satisfies predicate @p@.
--type None f p = (Not (Any f p) :: Predicate (f k))

---- | A @'NotAll' f p@ is a predicate on a collection @as@ that at least one
---- @a@ in @as@ does not satisfy predicate @p@.
--type NotAll f p = (Not (All f p) :: Predicate (f k))

---- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
---- a collection @as@ that is true if and only if /any/ item in @as@
---- satisfies the original predicate.
----
---- That is, it turns a predicate of kind @k ~> Type@ into a predicate
---- of kind @f k ~> Type@.
----
---- Essentially tests existential quantification.
--decideAny
--    :: forall f k (p :: k ~> Type). Universe f
--    => Decide p                                 -- ^ predicate on value
--    -> Decide (Any f p)                -- ^ predicate on collection
--decideAny f = idecideAny (const f)

---- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
---- a collection @as@ that is true if and only if /all/ items in @as@
---- satisfies the original predicate.
----
---- That is, it turns a predicate of kind @k ~> Type@ into a predicate
---- of kind @f k ~> Type@.
----
---- Essentially tests universal quantification.
--decideAll
--    :: forall f k (p :: k ~> Type). Universe f
--    => Decide p                                 -- ^ predicate on value
--    -> Decide (All f p)                -- ^ predicate on collection
--decideAll f = idecideAll (const f)

------ | If @p a@ is true for all values @a@ in @as@ under some
------ (Applicative) context @h@, then you can create an @'All' p as@ under
------ that Applicative context @h@.
------
------ Can be useful with 'Identity' (which is basically unwrapping and
------ wrapping 'All'), or with 'Maybe' (which can express predicates that
------ are either provably true or not provably false).
------
------ In practice, this can be used to iterate and traverse and sequence
------ actions over all "items" in @as@.
----genAllA
----    :: forall f k (p :: k ~> Type) (as :: f k) h. (Universe f, Applicative h)
----    => (forall a. Sing a -> h (p @@ a))        -- ^ predicate on value in context
----    -> (Sing as -> h (All f p @@ as))               -- ^ predicate on collection in context
----genAllA f = igenAllA (const f)

-- | 'genAll', but providing an 'Elem'.
igenAll
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> p @@ a)            -- ^ always-true predicate on value
    -> (Sing as -> All f p @@ as)                                  -- ^ always-true predicate on collection
igenAll f = prodAll (\(i :*: x) -> f i x) . imapProd (:*:) . singProd

-- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- p as@.  Basically witnesses the definition of 'All'.
genAll
    :: forall f k (p :: k ~> Type). Universe f
    => Prove p                 -- ^ always-true predicate on value
    -> Prove (All f p)         -- ^ always-true predicate on collection
genAll f = prodAll f . singProd

-- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
singAll
    :: forall f k (as :: f k). Universe f
    => Sing as
    -> All f Evident @@ as
singAll = prodAll id . singProd

---- | Automatically generate a witness for a member, if possible
--pickElem
--    :: forall f k (as :: f k) a. (Universe f, SingI as, SingI a, SDecide k)
--    => Decision (Elem f as a)
--pickElem = mapDecision (\case WitAny i Refl -> i)
--                       (\case i -> WitAny i Refl)
--         . decide @(Any f (TyPred ((:~:) a)))
--         $ sing

--instance (SingI (as :: [k]), SDecide k) => Decidable (TyPred (Index as)) where
--    decide x = withSingI x $ pickElem

--instance Universe [] where
--    allProd
--        :: forall p g. ()
--        => (forall a. Sing a -> p @@ a -> g a)
--        -> All [] p --> TyPred (Prod [] g)
--    allProd f = go
--      where
--        go :: Sing as -> WitAll [] p as -> Prod [] g as
--        go = \case
--          SNil         -> \_ -> RNil
--          x `SCons` xs -> \a -> f x (runWitAll a IZ)
--                             :& go xs (WitAll (runWitAll a . IS))

--    prodAll
--        :: forall p g as. ()
--        => (forall a. g a -> p @@ a)
--        -> Prod [] g as
--        -> All [] p @@ as
--    prodAll f = go
--      where
--        go :: Prod [] g bs -> All [] p @@ bs
--        go = \case
--          RNil    -> WitAll $ \case {}
--          x :& xs -> WitAll $ \case
--            IZ   -> f x
--            IS i -> runWitAll (go xs) i

--instance (SingI (as :: Maybe k), SDecide k) => Decidable (TyPred (IJust as)) where
--    decide x = withSingI x $ pickElem

-- | Test that a 'Maybe' is 'Just'.
--
-- @since 0.1.2.0
type IsJust    = (NotNull Maybe :: Predicate (Maybe k))

-- | Test that a 'Maybe' is 'Nothing'.
--
-- @since 0.1.2.0
type IsNothing = (Null    Maybe :: Predicate (Maybe k))

--instance Universe Maybe where
--    idecideAny f = \case
--      SNothing -> Disproved $ \case WitAny i _ -> case i of {}
--      SJust x  -> case f IJust x of
--        Proved p    -> Proved $ WitAny IJust p
--        Disproved v -> Disproved $ \case
--          WitAny IJust p -> v p

--    idecideAll f = \case
--      SNothing -> Proved $ WitAll $ \case {}
--      SJust x  -> case f IJust x of
--        Proved p    -> Proved $ WitAll $ \case IJust -> p
--        Disproved v -> Disproved $ \a -> v $ runWitAll a IJust

--instance (SingI (as :: Either j k), SDecide k) => Decidable (TyPred (IRight as)) where
--    decide x = withSingI x $ pickElem

-- | Test that an 'Either' is 'Right'
--
-- @since 0.1.2.0
type IsRight = (NotNull (Either j) :: Predicate (Either j k))

-- | Test that an 'Either' is 'Left'
--
-- @since 0.1.2.0
type IsLeft  = (Null    (Either j) :: Predicate (Either j k))

--instance Universe (Either j) where
--    idecideAny f = \case
--      SLeft  _ -> Disproved $ \case WitAny i _ -> case i of {}
--      SRight x -> case f IRight x of
--        Proved p    -> Proved $ WitAny IRight p
--        Disproved v -> Disproved $ \case
--          WitAny IRight p -> v p

--    idecideAll f = \case
--      SLeft  _ -> Proved $ WitAll $ \case {}
--      SRight x -> case f IRight x of
--        Proved p    -> Proved $ WitAll $ \case IRight -> p
--        Disproved v -> Disproved $ \a -> v $ runWitAll a IRight

--    -- igenAllA f = \case
--    --   SLeft  _ -> pure $ WitAll $ \case {}
--    --   SRight x -> (\p -> WitAll $ \case IRight -> p) <$> f IRight x

--instance (SingI (as :: NonEmpty k), SDecide k) => Decidable (TyPred (NEIndex as)) where
--    decide x = withSingI x $ pickElem

--instance Universe NonEmpty where
--    idecideAny
--        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
--        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
--        -> Sing as
--        -> Decision (Any NonEmpty p @@ as)
--    idecideAny f (x NE.:%| xs) = case f NEHead x of
--      Proved p    -> Proved $ WitAny NEHead p
--      Disproved v -> case idecideAny @[] @_ @p (f . NETail) xs of
--        Proved (WitAny i p) -> Proved $ WitAny (NETail i) p
--        Disproved vs     -> Disproved $ \case
--          WitAny i p -> case i of
--            NEHead    -> v p
--            NETail i' -> vs (WitAny i' p)

--    idecideAll
--        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
--        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
--        -> Sing as
--        -> Decision (All NonEmpty p @@ as)
--    idecideAll f (x NE.:%| xs) = case f NEHead x of
--      Proved p -> case idecideAll @[] @_ @p (f . NETail) xs of
--        Proved ps -> Proved $ WitAll $ \case
--          NEHead   -> p
--          NETail i -> runWitAll ps i
--        Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . NETail)
--      Disproved v -> Disproved $ \a -> v $ runWitAll a NEHead

--    -- igenAllA
--    --     :: forall k (p :: k ~> Type) (as :: NonEmpty k) h. Applicative h
--    --     => (forall a. Elem NonEmpty as a -> Sing a -> h (p @@ a))
--    --     -> Sing as
--    --     -> h (All NonEmpty p @@ as)
--    -- igenAllA f (x NE.:%| xs) = go <$> f NEHead x <*> igenAllA @[] @_ @p (f . NETail) xs
--    --   where
--    --     go :: p @@ b -> All [] p @@ bs -> All NonEmpty p @@ (b ':| bs)
--    --     go p ps = WitAll $ \case
--    --       NEHead   -> p
--    --       NETail i -> runWitAll ps i

---- TODO: does this interfere with NonNull stuff?
--instance (SingI (as :: (j, k)), SDecide k) => Decidable (TyPred (ISnd as)) where
--    decide x = withSingI x $ pickElem

--instance Universe ((,) j) where
--    idecideAny f (STuple2 _ x) = case f ISnd x of
--      Proved p    -> Proved $ WitAny ISnd p
--      Disproved v -> Disproved $ \case WitAny ISnd p -> v p

--    idecideAll f (STuple2 _ x) = case f ISnd x of
--      Proved p    -> Proved $ WitAll $ \case ISnd -> p
--      Disproved v -> Disproved $ \a -> v $ runWitAll a ISnd

--    -- igenAllA f (STuple2 _ x) = (\p -> WitAll $ \case ISnd -> p) <$> f ISnd x

---- | The null universe
--instance Universe Proxy where
--    idecideAny _ _ = Disproved $ \case
--        WitAny i _ -> case i of {}
--    idecideAll _ _ = Proved $ WitAll $ \case {}

--    -- igenAllA   _ _ = pure $ WitAll $ \case {}

--instance (SingI (as :: Identity k), SDecide k) => Decidable (TyPred (IIdentity as)) where
--    decide x = withSingI x $ pickElem

---- | The single-pointed universe.  Note that this instance is really only
---- usable in /singletons-2.5/ and higher (so GHC 8.6).
--instance Universe Identity where
--    idecideAny f (SIdentity x) = mapDecision (WitAny IId)
--                                             (\case WitAny IId p -> p)
--                               $ f IId x
--    idecideAll f (SIdentity x) = mapDecision (\p -> WitAll $ \case IId -> p)
--                                             (`runWitAll` IId)
--                               $ f IId x

--    -- igenAllA f (SIdentity x) = (\p -> WitAll $ \case IId -> p) <$> f IId x

---- instance forall f g a f' g' a'. (SingKind (f (g a)), Demote (f (g a)) ~ f' (g' a')) => SingKind ((f :.: g) a) where
----     type Demote ((f :.: g) a) = (:.:) f' g' a'

---- deriving instance ((forall as. Show (Elem f ass as)), (forall as. Show (Elem g as a)))
----     => Show (CompElem ('Comp ass :: (f :.: g) k) a)

