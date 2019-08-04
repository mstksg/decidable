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

module Data.Type.Universe.Internal (
  -- * Universe
    Elem, In, Prod, HasProd(..), Universe(..)
  -- , mapProd
  , imapProd
  -- , foldMapProd, ifoldMapProd
  -- , splitSing
  -- -- ** Instances
  -- , Index(..), IJust(..), IRight(..), NEIndex(..), ISnd(..), IProxy, IIdentity(..)
  -- , CompElem(..), SumElem(..)
  -- , sameIndexVal, sameNEIndexVal
  -- ** Predicates
  , All, WitAll(..), NotAll
  , Any, WitAny(..), None
  , Null, NotNull
  -- -- *** Specialized
  -- , IsJust, IsNothing, IsRight, IsLeft
  -- * Decisions and manipulations
  , decideAny, decideAll
  -- , genAll, igenAll
  -- , foldMapUni, ifoldMapUni
  , index, pickElem
  -- -- * Universe Combination
  -- -- ** Universe Composition
  -- , (:.:)(..), sGetComp, GetComp
  -- , allComp, compAll, anyComp, compAny
  -- -- ** Universe Disjunction
  -- , (:+:)(..)
  -- , anySumL, anySumR, sumLAny, sumRAny
  -- , allSumL, allSumR, sumLAll, sumRAll
  -- * Defunctionalization symbols
  , ElemSym0, ElemSym1, ElemSym2
  , ProdSym0, ProdSym1, ProdSym2
  -- , GetCompSym0, GetCompSym1
  -- -- * Singletons
  -- , SIndex(..), SIJust(..), SIRight(..), SNEIndex(..), SISnd(..), SIProxy, SIIdentity(..)
  -- , Sing (SComp, SInL, SIndex', SIJust', SIRight', SNEIndex', SISnd', SIProxy', SIIdentity')
  ) where

import           Control.Applicative
import           Data.Functor
import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty                    (NonEmpty(..))
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding        (Elem, ElemSym0, ElemSym1, ElemSym2, Any, All, Null, Not)
import           Data.Singletons.Prelude.Identity
import           Data.Type.Predicate
import           Data.Type.Predicate.Logic
import           Data.Typeable                         (Typeable)
import           Data.Vinyl                            (Rec(..))
import           GHC.Generics                          (Generic, (:*:)(..))
import           Prelude hiding                        (any, all)
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

-- | A witness for membership of a given item in a type-level collection
type family Elem (f :: Type -> Type) = (i :: f k -> k -> Type) | i -> f

data ElemSym0 (f :: Type -> Type) :: f k ~> k ~> Type
data ElemSym1 (f :: Type -> Type) :: f k -> k ~> Type
type ElemSym2 (f :: Type -> Type) (as :: f k) (a :: k) = Elem f as a

type instance Apply (ElemSym0 f) as = ElemSym1 f as
type instance Apply (ElemSym1 f as) a = Elem f as a

type family Prod (f :: Type -> Type) = (p :: (k -> Type) -> f k -> Type) | p -> f

data ProdSym0 (f :: Type -> Type) :: (k -> Type) ~> f k ~> Type
data ProdSym1 (f :: Type -> Type) :: (k -> Type) -> f k ~> Type
type ProdSym2 (f :: Type -> Type) (g :: k -> Type) (as :: f k) = Prod f g as

type instance Apply (ProdSym0 f) g = ProdSym1 f g
type instance Apply (ProdSym1 f g) as = Prod f g as

-- | @'In' f as@ is a predicate that a given input @a@ is a member of
-- collection @as@.
type In (f :: Type -> Type) (as :: f k) = ElemSym1 f as

-- instance (Universe f, Decidable p) => Decidable (Any f p) where
--     decide = decideAny @f @_ @p $ decide @p

-- instance (Universe f, Decidable p) => Decidable (All f p) where
--     decide = decideAll @f @_ @p $ decide @p

-- instance (Universe f, Provable p) => Decidable (NotNull f ==> Any f p) where

-- instance Provable p => Provable (NotNull f ==> Any f p) where
--     prove _ (WitAny i s) = WitAny i (prove @p s)

-- instance (Universe f, Provable p) => Provable (All f p) where
--     prove xs = WitAll $ \i -> prove @p (index i xs)

-- instance Universe f => TFunctor (Any f) where
--     tmap f xs (WitAny i x) = WitAny i (f (index i xs) x)

-- instance Universe f => TFunctor (All f) where
--     tmap f xs a = WitAll $ \i -> f (index i xs) (runWitAll a i)

-- instance Universe f => DFunctor (All f) where
--     dmap f xs a = idecideAll (\i x -> f x (runWitAll a i)) xs

class HasProd (f :: Type -> Type) where
    singProd :: Sing as -> Prod f Sing as
    prodSing :: Prod f Sing as -> Sing as

    itraverseProd
        :: Applicative m
        => (forall a. Elem f as a -> g a -> m (h a))
        -> Prod f g as
        -> m (Prod f h as)

    traverseProd
        :: Applicative m
        => (forall a. g a -> m (h a))
        -> Prod f g as
        -> m (Prod f h as)
    traverseProd f = itraverseProd (const f)

    zipWithProd
        :: (forall a. g a -> h a -> j a)
        -> Prod f g as
        -> Prod f h as
        -> Prod f j as
    zipWithProd f xs ys = imapProd (\i x -> f x (indexProd i ys)) xs

    indexProd
        :: Elem f as a
        -> Prod f g as
        -> g a


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
newtype WitAll f p (as :: f k) = WitAll { runWitAll :: forall a. Elem f as a -> p @@ a }

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

instance (Universe f, Provable p) => Decidable (NotNull f ==> Any f p) where

instance Provable p => Provable (NotNull f ==> Any f p) where
    prove _ (WitAny i s) = WitAny i (prove @p s)

instance (Universe f, Provable p) => Provable (All f p) where
    prove xs = WitAll $ \i -> prove @p (index i xs)

instance Universe f => TFunctor (Any f) where
    tmap f xs (WitAny i x) = WitAny i (f (index i xs) x)

instance Universe f => TFunctor (All f) where
    tmap f xs a = WitAll $ \i -> f (index i xs) (runWitAll a i)

instance Universe f => DFunctor (All f) where
    dmap f xs a = idecideAll (\i x -> f x (runWitAll a i)) xs

-- | Typeclass for a type-level container that you can quantify or lift
-- type-level predicates over.
class HasProd f => Universe (f :: Type -> Type) where
    -- | 'decideAny', but providing an 'Elem'.
    idecideAny
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
        -> (Sing as -> Decision (Any f p @@ as))                         -- ^ predicate on collection

    -- | 'decideAll', but providing an 'Elem'.
    idecideAll
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
        -> (Sing as -> Decision (All f p @@ as))                         -- ^ predicate on collection

    allProd
        :: forall p g. ()
        => (forall a. Sing a -> p @@ a -> g a)
        -> All f p --> TyPred (Prod f g)
    prodAll
        :: forall p g as. ()
        => (forall a. g a -> p @@ a)
        -> Prod f g as
        -> All f p @@ as

-- | Predicate that a given @as :: f k@ is empty and has no items in it.
type Null    f = (None f Evident :: Predicate (f k))

-- | Predicate that a given @as :: f k@ is not empty, and has at least one
-- item in it.
type NotNull f = (Any f Evident :: Predicate (f k))

-- | A @'None' f p@ is a predicate on a collection @as@ that no @a@ in @as@
-- satisfies predicate @p@.
type None f p = (Not (Any f p) :: Predicate (f k))

-- | A @'NotAll' f p@ is a predicate on a collection @as@ that at least one
-- @a@ in @as@ does not satisfy predicate @p@.
type NotAll f p = (Not (All f p) :: Predicate (f k))

imapProd
    :: HasProd f
    => (forall a. Elem f as a -> g a -> h a)
    -> Prod f g as
    -> Prod f h as
imapProd f = runIdentity . itraverseProd (\i -> Identity . f i)

-- | Extract the item from the container witnessed by the 'Elem'
index
    :: forall f as a. HasProd f
    => Elem f as a        -- ^ Witness
    -> Sing as            -- ^ Collection
    -> Sing a
index i = indexProd i . singProd

-- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
-- a collection @as@ that is true if and only if /any/ item in @as@
-- satisfies the original predicate.
--
-- That is, it turns a predicate of kind @k ~> Type@ into a predicate
-- of kind @f k ~> Type@.
--
-- Essentially tests existential quantification.
decideAny
    :: forall f k (p :: k ~> Type). Universe f
    => Decide p                                 -- ^ predicate on value
    -> Decide (Any f p)                -- ^ predicate on collection
decideAny f = idecideAny (const f)

-- | Lifts a predicate @p@ on an individual @a@ into a predicate that on
-- a collection @as@ that is true if and only if /all/ items in @as@
-- satisfies the original predicate.
--
-- That is, it turns a predicate of kind @k ~> Type@ into a predicate
-- of kind @f k ~> Type@.
--
-- Essentially tests universal quantification.
decideAll
    :: forall f k (p :: k ~> Type). Universe f
    => Decide p                                 -- ^ predicate on value
    -> Decide (All f p)                -- ^ predicate on collection
decideAll f = idecideAll (const f)

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

---- | 'genAll', but providing an 'Elem'.
--igenAll
--    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
--    => (forall a. Elem f as a -> Sing a -> p @@ a)            -- ^ always-true predicate on value
--    -> (Sing as -> All f p @@ as)                                  -- ^ always-true predicate on collection
--igenAll f = prodAll (\(i :*: x) -> f i x) . imapProd (:*:) . singProd

---- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
---- p as@.  Basically witnesses the definition of 'All'.
--genAll
--    :: forall f k (p :: k ~> Type). Universe f
--    => Prove p                 -- ^ always-true predicate on value
--    -> Prove (All f p)         -- ^ always-true predicate on collection
--genAll f = prodAll f . singProd

---- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
--splitSing
--    :: forall f k (as :: f k). Universe f
--    => Sing as
--    -> All f (TyPred Sing) @@ as
--splitSing = prodAll id . singProd

-- | Automatically generate a witness for a member, if possible
pickElem
    :: forall f k (as :: f k) a. (Universe f, SingI as, SingI a, SDecide k)
    => Decision (Elem f as a)
pickElem = mapDecision (\case WitAny i Refl -> i)
                       (\case i -> WitAny i Refl)
         . decide @(Any f (TyPred ((:~:) a)))
         $ sing

--instance (SingI (as :: [k]), SDecide k) => Decidable (TyPred (Index as)) where
--    decide x = withSingI x $ pickElem

--instance Universe [] where
--    idecideAny
--        :: forall k (p :: k ~> Type) (as :: [k]). ()
--        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
--        -> Sing as
--        -> Decision (Any [] p @@ as)
--    idecideAny f = \case
--      SNil -> Disproved $ \case
--        WitAny i _ -> case i of {}
--      x `SCons` xs -> case f IZ x of
--        Proved p    -> Proved $ WitAny IZ p
--        Disproved v -> case idecideAny @[] @_ @p (f . IS) xs of
--          Proved (WitAny i p) -> Proved $ WitAny (IS i) p
--          Disproved vs -> Disproved $ \case
--            WitAny IZ     p -> v p
--            WitAny (IS i) p -> vs (WitAny i p)

--    idecideAll
--        :: forall k (p :: k ~> Type) (as :: [k]). ()
--        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
--        -> Sing as
--        -> Decision (All [] p @@ as)
--    idecideAll f = \case
--      SNil -> Proved $ WitAll $ \case {}
--      x `SCons` xs -> case f IZ x of
--        Proved p -> case idecideAll @[] @_ @p (f . IS) xs of
--          Proved a -> Proved $ WitAll $ \case
--            IZ   -> p
--            IS i -> runWitAll a i
--          Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . IS)
--        Disproved v -> Disproved $ \a -> v $ runWitAll a IZ

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

---- | Test that a 'Maybe' is 'Just'.
----
---- @since 0.1.2.0
--type IsJust    = (NotNull Maybe :: Predicate (Maybe k))

---- | Test that a 'Maybe' is 'Nothing'.
----
---- @since 0.1.2.0
--type IsNothing = (Null    Maybe :: Predicate (Maybe k))

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

---- | Test that an 'Either' is 'Right'
----
---- @since 0.1.2.0
--type IsRight = (NotNull (Either j) :: Predicate (Either j k))

---- | Test that an 'Either' is 'Left'
----
---- @since 0.1.2.0
--type IsLeft  = (Null    (Either j) :: Predicate (Either j k))

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

--instance (Universe f, Universe g) => Universe (f :.: g) where
--    idecideAny
--        :: forall k (p :: k ~> Type) (ass :: (f :.: g) k). ()
--        => (forall a. Elem (f :.: g) ass a -> Sing a -> Decision (p @@ a))
--        -> Sing ass
--        -> Decision (Any (f :.: g) p @@ ass)
--    idecideAny f (SComp xss)
--        = mapDecision anyComp compAny
--        . idecideAny @f @_ @(Any g p) go
--        $ xss
--      where
--        go  :: Elem f (GetComp ass) as
--            -> Sing as
--            -> Decision (Any g p @@ as)
--        go i = idecideAny $ \j -> f (i :? j)

--    idecideAll
--        :: forall k (p :: k ~> Type) (ass :: (f :.: g) k). ()
--        => (forall a. Elem (f :.: g) ass a -> Sing a -> Decision (p @@ a))
--        -> Sing ass
--        -> Decision (All (f :.: g) p @@ ass)
--    idecideAll f (SComp xss)
--        = mapDecision allComp compAll
--        . idecideAll @f @_ @(All g p) go
--        $ xss
--      where
--        go  :: Elem f (GetComp ass) as
--            -> Sing as
--            -> Decision (All g p @@ as)
--        go i = idecideAll $ \j -> f (i :? j)

--    -- igenAllA
--    --     :: forall k (p :: k ~> Type) (ass :: (f :.: g) k) h. Applicative h
--    --     => (forall a. Elem (f :.: g) ass a -> Sing a -> h (p @@ a))
--    --     -> Sing ass
--    --     -> h (All (f :.: g) p @@ ass)
--    -- igenAllA f (SComp ass) = allComp <$> igenAllA @f @_ @(All g p) go ass
--    --   where
--    --     go  :: Elem f (GetComp ass) (as :: g k)
--    --         -> Sing as
--    --         -> h (All g p @@ as)
--    --     go i = igenAllA $ \j -> f (i :? j)

---- | Turn a composition of 'Any' into an 'Any' of a composition.
----
---- @since 0.1.2.0
--anyComp :: Any f (Any g p) @@ as -> Any (f :.: g) p @@ 'Comp as
--anyComp (WitAny i (WitAny j p)) = WitAny (i :? j) p

---- | Turn an 'Any' of a composition into a composition of 'Any'.
----
---- @since 0.1.2.0
--compAny :: Any (f :.: g) p @@ 'Comp as -> Any f (Any g p) @@ as
--compAny (WitAny (i :? j) p) = WitAny i (WitAny j p)

---- | Turn a composition of 'All' into an 'All' of a composition.
----
---- @since 0.1.2.0
--allComp :: All f (All g p) @@ as -> All (f :.: g) p @@ 'Comp as
--allComp a = WitAll $ \(i :? j) -> runWitAll (runWitAll a i) j

---- | Turn an 'All' of a composition into a composition of 'All'.
----
---- @since 0.1.2.0
--compAll :: All (f :.: g) p @@ 'Comp as -> All f (All g p) @@ as
--compAll a = WitAll $ \i -> WitAll $ \j -> runWitAll a (i :? j)

--instance (Universe f, Universe g) => Universe (f :+: g) where
--    idecideAny
--        :: forall k (p :: k ~> Type) (abs :: (f :+: g) k). ()
--        => (forall ab. Elem (f :+: g) abs ab -> Sing ab -> Decision (p @@ ab))
--        -> Sing abs
--        -> Decision (Any (f :+: g) p @@ abs)
--    idecideAny f = \case
--      SInL xs -> mapDecision anySumL sumLAny
--               $ idecideAny @f @_ @p (f . IInL) xs
--      SInR ys -> mapDecision anySumR sumRAny
--               $ idecideAny @g @_ @p (f . IInR) ys

--    idecideAll
--        :: forall k (p :: k ~> Type) (abs :: (f :+: g) k). ()
--        => (forall ab. Elem (f :+: g) abs ab -> Sing ab -> Decision (p @@ ab))
--        -> Sing abs
--        -> Decision (All (f :+: g) p @@ abs)
--    idecideAll f = \case
--      SInL xs -> mapDecision allSumL sumLAll
--               $ idecideAll @f @_ @p (f . IInL) xs
--      SInR xs -> mapDecision allSumR sumRAll
--               $ idecideAll @g @_ @p (f . IInR) xs

--    -- igenAllA
--    --     :: forall k (p :: k ~> Type) (abs :: (f :+: g) k) h. Applicative h
--    --     => (forall ab. Elem (f :+: g) abs ab -> Sing ab -> h (p @@ ab))
--    --     -> Sing abs
--    --     -> h (All (f :+: g) p @@ abs)
--    -- igenAllA f = \case
--    --   SInL xs -> allSumL <$> igenAllA @f @_ @p (f . IInL) xs
--    --   SInR xs -> allSumR <$> igenAllA @g @_ @p (f . IInR) xs

---- | Turn an 'Any' of @f@ into an 'Any' of @f ':+:' g@.
--anySumL :: Any f p @@ as -> Any (f :+: g) p @@ 'InL as
--anySumL (WitAny i x) = WitAny (IInL i) x

---- | Turn an 'Any' of @g@ into an 'Any' of @f ':+:' g@.
--anySumR :: Any g p @@ bs -> Any (f :+: g) p @@ 'InR bs
--anySumR (WitAny j y) = WitAny (IInR j) y

---- | Turn an 'Any' of @f ':+:' g@ into an 'Any' of @f@.
--sumLAny :: Any (f :+: g) p @@ 'InL as -> Any f p @@ as
--sumLAny (WitAny (IInL i) x) = WitAny i x

---- | Turn an 'Any' of @f ':+:' g@ into an 'Any' of @g@.
--sumRAny :: Any (f :+: g) p @@ 'InR bs -> Any g p @@ bs
--sumRAny (WitAny (IInR j) y) = WitAny j y

---- | Turn an 'All' of @f@ into an 'All' of @f ':+:' g@.
--allSumL :: All f p @@ as -> All (f :+: g) p @@ 'InL as
--allSumL a = WitAll $ \case IInL i -> runWitAll a i

---- | Turn an 'All' of @g@ into an 'All' of @f ':+:' g@.
--allSumR :: All g p @@ bs -> All (f :+: g) p @@ 'InR bs
--allSumR a = WitAll $ \case IInR j -> runWitAll a j

---- | Turn an 'All' of @f ':+:' g@ into an 'All' of @f@.
--sumLAll :: All (f :+: g) p @@ 'InL as -> All f p @@ as
--sumLAll a = WitAll $ runWitAll a . IInL

---- | Turn an 'All' of @f ':+:' g@ into an 'All' of @g@.
--sumRAll :: All (f :+: g) p @@ 'InR bs -> All g p @@ bs
--sumRAll a = WitAll $ runWitAll a . IInR
