{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
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
{-# LANGUAGE UndecidableInstances   #-}

module Data.Type.Universe.Prod (

  -- * Prod
    Elem, In, Prod, HasProd(..)
  , mapProd, imapProd, foldMapProd, ifoldMapProd, itraverseProd
  -- ** Instances
  , Rec(..), Index(..)
  , PMaybe(..), IJust(..)
  , PEither(..), IRight(..)
  , NERec(..), NEIndex(..)
  , PTup(..), ISnd(..)
  , PProxy(..), IProxy
  , PIdentity(..), IIdentity(..)
  , CompProd(..), CompElem(..), _CompProd
  , PSum(..), SumElem(..), _PInL, _PInR
  , sameIndexVal, sameNEIndexVal
  -- * Manipulations
  , foldMapUni, ifoldMapUni, index, indexProd
  , pickElem
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
  , Sing (SComp, SInR, SInL, SIndex', SIJust', SIRight', SNEIndex', SISnd', SIProxy', SIIdentity')

  ) where

import           Control.Applicative
import           Data.Functor
import           Data.Functor.Classes
import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty                    (NonEmpty(..))
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding        (Elem, ElemSym0, ElemSym1, ElemSym2, Any, All, Null, Not)
import           Data.Singletons.Prelude.Identity
import           Data.Type.Predicate
import           Data.Type.Universe.Internal
import           Data.Typeable                         (Typeable)
import           Data.Vinyl                            (Rec(..))
import           GHC.Generics                          (Generic, (:*:)(..))
import           Lens.Micro                            (Lens', Lens, lens)
import           Prelude hiding                        (any, all)
import           Unsafe.Coerce
import qualified Data.Singletons.Prelude.Either        as S
import qualified Data.Singletons.Prelude.List.NonEmpty as NE
import qualified Data.Singletons.Prelude.Maybe         as S
import qualified Data.Vinyl                            as V
import qualified Data.Vinyl.Functor                    as V

itraverseProd
    :: (HasProd f, Applicative m)
    => (forall a. Elem f as a -> g a -> m (h a))
    -> Prod f g as
    -> m (Prod f h as)
itraverseProd f = traverseProd (\(i :*: x) -> f i x) . withIndices

ifoldMapProd
    :: (HasProd f, Monoid m)
    => (forall a. Elem f as a -> g a -> m)
    -> Prod f g as
    -> m
ifoldMapProd f = getConst . itraverseProd (\i -> Const . f i)

foldMapProd
    :: (HasProd f, Monoid m)
    => (forall a. g a -> m)
    -> Prod f g as
    -> m
foldMapProd f = ifoldMapProd (const f)

-- -- | 'genAll', but providing an 'Elem'.
-- igenAll
--     :: forall f k (p :: k ~> Type) (as :: f k). HasProd f
--     => (forall a. Elem f as a -> Sing a -> p @@ a)            -- ^ always-true predicate on value
--     -> (Sing as -> All f p @@ as)                                  -- ^ always-true predicate on collection
-- igenAll f = prodAll (\(i :*: x) -> f i x) . imapProd (:*:) . singProd

-- -- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- -- p as@.  Basically witnesses the definition of 'All'.
-- genAll
--     :: forall f k (p :: k ~> Type). HasProd f
--     => Prove p                 -- ^ always-true predicate on value
--     -> Prove (All f p)         -- ^ always-true predicate on collection
-- genAll f = prodAll f . singProd

-- | 'foldMapUni' but with access to the index.
ifoldMapUni
    :: forall f k (as :: f k) m. (HasProd f, Monoid m)
    => (forall a. Elem f as a -> Sing a -> m)
    -> Sing as
    -> m
ifoldMapUni f = ifoldMapProd f . singProd

-- | A 'foldMap' over all items in a collection.
foldMapUni
    :: forall f k (as :: f k) m. (HasProd f, Monoid m)
    => (forall (a :: k). Sing a -> m)
    -> Sing as
    -> m
foldMapUni f = ifoldMapUni (const f)

-- | Witness an item in a type-level list by providing its index.
data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

deriving instance Show (Index as a)

instance (SingI (as :: [k]), SDecide k) => Decidable (TyPred (Index as)) where
    decide x = withSingI x $ pickElem

type instance Elem [] = Index
type instance Prod [] = Rec

-- | Kind-indexed singleton for 'Index'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIndex'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIndex as a :: Index as a -> Type where
    SIZ :: SIndex (a ': as) a 'IZ
    SIS :: SIndex bs a i -> SIndex (b ': bs) a ('IS i)

deriving instance Show (SIndex as a i)

newtype instance Sing (i :: Index as a) where
    SIndex' :: SIndex as a i -> Sing i

instance SingI 'IZ where
    sing = SIndex' SIZ

instance SingI i => SingI ('IS i) where
    sing = case sing of
      SIndex' i -> SIndex' (SIS i)

instance SingKind (Index as a) where
    type Demote (Index as a) = Index as a
    fromSing (SIndex' i) = go i
      where
        go :: SIndex bs b i -> Index bs b
        go = \case
          SIZ   -> IZ
          SIS j -> IS (go j)
    toSing i = go i (SomeSing . SIndex')
      where
        go :: Index bs b -> (forall i. SIndex bs b i -> r) -> r
        go = \case
          IZ   -> ($ SIZ)
          IS j -> \f -> go j (f . SIS)

instance SDecide (Index as a) where
    SIndex' i %~ SIndex' j = go i j
      where
        go :: SIndex bs b i -> SIndex bs b j -> Decision (i :~: j)
        go = \case
          SIZ -> \case
            SIZ   -> Proved Refl
            SIS _ -> Disproved $ \case {}
          SIS i' -> \case
            SIZ   -> Disproved $ \case {}
            SIS j' -> case go i' j' of
              Proved Refl -> Proved Refl
              Disproved v -> Disproved $ \case Refl -> v Refl

instance HasProd [] where

    singProd = \case
      SNil         -> RNil
      x `SCons` xs -> x :& singProd xs

    traverseProd
        :: forall g h m as. Applicative m
        => (forall a. g a -> m (h a))
        -> Prod [] g as
        -> m (Prod [] h as)
    traverseProd f = go
      where
        go :: Prod [] g bs -> m (Prod [] h bs)
        go = \case
          RNil    -> pure RNil
          x :& xs -> (:&) <$> f x <*> go xs

    zipWithProd
        :: forall g h j as. ()
        => (forall a. g a -> h a -> j a)
        -> Prod [] g as
        -> Prod [] h as
        -> Prod [] j as
    zipWithProd f = go
      where
        go :: Prod [] g bs -> Prod [] h bs -> Prod [] j bs
        go = \case
          RNil -> \case
            RNil -> RNil
          x :& xs -> \case
            y :& ys -> f x y :& go xs ys

    withIndices = \case
        RNil    -> RNil
        x :& xs -> (IZ :*: x) :& mapProd (\(i :*: y) -> IS i :*: y) (withIndices xs)

    ixProd
        :: forall g as a. ()
        => Elem [] as a
        -> Lens' (Prod [] g as) (g a)
    ixProd i0 (f :: g a -> h (g a)) = go i0
      where
        go :: Elem [] bs a -> Prod [] g bs -> h (Prod [] g bs)
        go = \case
          IZ -> \case
            x :& xs -> (:& xs) <$> f x
          IS i -> \case
            x :& xs -> (x :&) <$> go i xs

    allProd
        :: forall p g. ()
        => (forall a. Sing a -> p @@ a -> g a)
        -> All [] p --> TyPred (Prod [] g)
    allProd f = go
      where
        go :: Sing as -> WitAll [] p as -> Prod [] g as
        go = \case
          SNil         -> \_ -> RNil
          x `SCons` xs -> \a -> f x (runWitAll a IZ)
                             :& go xs (WitAll (runWitAll a . IS))

    prodAll
        :: forall p g as. ()
        => (forall a. g a -> p @@ a)
        -> Prod [] g as
        -> All [] p @@ as
    prodAll f = go
      where
        go :: Prod [] g bs -> All [] p @@ bs
        go = \case
          RNil    -> WitAll $ \case {}
          x :& xs -> WitAll $ \case
            IZ   -> f x
            IS i -> runWitAll (go xs) i


instance Universe [] where
    idecideAny
        :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any [] p @@ as)
    idecideAny f = \case
      SNil -> Disproved $ \case
        WitAny i _ -> case i of {}
      x `SCons` xs -> case f IZ x of
        Proved p    -> Proved $ WitAny IZ p
        Disproved v -> case idecideAny @[] @_ @p (f . IS) xs of
          Proved (WitAny i p) -> Proved $ WitAny (IS i) p
          Disproved vs -> Disproved $ \case
            WitAny IZ     p -> v p
            WitAny (IS i) p -> vs (WitAny i p)

    idecideAll
        :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All [] p @@ as)
    idecideAll f = \case
      SNil -> Proved $ WitAll $ \case {}
      x `SCons` xs -> case f IZ x of
        Proved p -> case idecideAll @[] @_ @p (f . IS) xs of
          Proved a -> Proved $ WitAll $ \case
            IZ   -> p
            IS i -> runWitAll a i
          Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . IS)
        Disproved v -> Disproved $ \a -> v $ runWitAll a IZ



-- | Test if two indices point to the same item in a list.
--
-- We have to return a 'Maybe' here instead of a 'Decision', because it
-- might be the case that the same item might be duplicated in a list.
-- Therefore, even if two indices are different, we cannot prove that the
-- values they point to are different.
--
-- @since 0.1.5.1
sameIndexVal
    :: Index as a
    -> Index as b
    -> Maybe (a :~: b)
sameIndexVal = \case
    IZ -> \case
      IZ   -> Just Refl
      IS _ -> Nothing
    IS i -> \case
      IZ   -> Nothing
      IS j -> sameIndexVal i j <&> \case Refl -> Refl

-- | Witness an item in a type-level 'Maybe' by proving the 'Maybe' is
-- 'Just'.
data IJust :: Maybe k -> k -> Type where
    IJust :: IJust ('Just a) a

deriving instance Show (IJust as a)

instance (SingI (as :: Maybe k), SDecide k) => Decidable (TyPred (IJust as)) where
    decide x = withSingI x $ pickElem

-- | Kind-indexed singleton for 'IJust'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIJust'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIJust as a :: IJust as a -> Type where
    SIJust :: SIJust ('Just a) a 'IJust

deriving instance Show (SIJust as a i)

newtype instance Sing (i :: IJust as a) where
    SIJust' :: SIJust as a i -> Sing i

instance SingI 'IJust where
    sing = SIJust' SIJust

instance SingKind (IJust as a) where
    type Demote (IJust as a) = IJust as a
    fromSing (SIJust' SIJust) = IJust
    toSing IJust = SomeSing (SIJust' SIJust)

instance SDecide (IJust as a) where
    SIJust' SIJust %~ SIJust' SIJust = Proved Refl

data PMaybe :: (k -> Type) -> Maybe k -> Type where
    PNothing :: PMaybe f 'Nothing
    PJust    :: f a -> PMaybe f ('Just a)

instance (V.ReifyConstraint Show f (S.MaybeToList as)) => Show (PMaybe f as) where
    showsPrec d = \case
      PNothing -> showString "PNothing"
      PJust x  -> case V.reifyConstraint @Show (x :& RNil) of
        V.Compose (V.Dict _) :& RNil -> showsUnaryWith showsPrec "PJust" d x

type instance Elem Maybe = IJust
type instance Prod Maybe = PMaybe

instance Provable (TyPred (PMaybe Sing)) where
    prove = singProd

instance HasProd Maybe where
    singProd = \case
      SNothing -> PNothing
      SJust x  -> PJust x
    withIndices = \case
      PNothing -> PNothing
      PJust x  -> PJust (IJust :*: x)
    traverseProd f = \case
      PNothing -> pure PNothing
      PJust x  -> PJust <$> f x
    zipWithProd f = \case
      PNothing -> \case
        PNothing -> PNothing
      PJust x -> \case
        PJust y -> PJust (f x y)
    ixProd = \case
      IJust -> \f -> \case
        PJust x -> PJust <$> f x
    allProd f = \case
      SNothing -> \_ -> PNothing
      SJust x  -> \a -> PJust (f x (runWitAll a IJust))
    prodAll f = \case
      PNothing -> WitAll $ \case {}
      PJust x  -> WitAll $ \case IJust -> f x

instance Universe Maybe where
    idecideAny f = \case
      SNothing -> Disproved $ \case WitAny i _ -> case i of {}
      SJust x  -> case f IJust x of
        Proved p    -> Proved $ WitAny IJust p
        Disproved v -> Disproved $ \case
          WitAny IJust p -> v p

    idecideAll f = \case
      SNothing -> Proved $ WitAll $ \case {}
      SJust x  -> case f IJust x of
        Proved p    -> Proved $ WitAll $ \case IJust -> p
        Disproved v -> Disproved $ \a -> v $ runWitAll a IJust


-- | Witness an item in a type-level @'Either' j@ by proving the 'Either'
-- is 'Right'.
data IRight :: Either j k -> k -> Type where
    IRight :: IRight ('Right a) a

deriving instance Show (IRight as a)

instance (SingI (as :: Either j k), SDecide k) => Decidable (TyPred (IRight as)) where
    decide x = withSingI x $ pickElem

-- | Kind-indexed singleton for 'IRight'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIRight'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIRight as a :: IRight as a -> Type where
    SIRight :: SIRight ('Right a) a 'IRight

deriving instance Show (SIRight as a i)

newtype instance Sing (i :: IRight as a) where
    SIRight' :: SIRight as a i -> Sing i

instance SingI 'IRight where
    sing = SIRight' SIRight

instance SingKind (IRight as a) where
    type Demote (IRight as a) = IRight as a
    fromSing (SIRight' SIRight) = IRight
    toSing IRight = SomeSing (SIRight' SIRight)

instance SDecide (IRight as a) where
    SIRight' SIRight %~ SIRight' SIRight = Proved Refl

data PEither :: (k -> Type) -> Either j k -> Type where
    PLeft  :: PEither f ('Left e)
    PRight :: f a -> PEither f ('Right a)

type instance Elem (Either j) = IRight
type instance Prod (Either j) = PEither

instance (V.ReifyConstraint Show f (S.Rights '[as])) => Show (PEither f as) where
    showsPrec d = \case
      PLeft    -> showString "PNothing"
      PRight x -> case V.reifyConstraint @Show (x :& RNil) of
        V.Compose (V.Dict _) :& RNil -> showsUnaryWith showsPrec "PRight" d x

instance Provable (TyPred (PEither Sing)) where
    prove = singProd

instance HasProd (Either j) where
    singProd = \case
      SLeft  _ -> PLeft
      SRight x -> PRight x
    withIndices = \case
      PLeft    -> PLeft
      PRight x -> PRight (IRight :*: x)
    traverseProd f = \case
      PLeft    -> pure PLeft
      PRight x -> PRight <$> f x
    zipWithProd f = \case
      PLeft -> \case
        PLeft -> PLeft
      PRight x -> \case
        PRight y -> PRight (f x y)
    ixProd = \case
      IRight -> \f -> \case
        PRight x -> PRight <$> f x
    allProd f = \case
      SLeft  _ -> \_ -> PLeft
      SRight x -> \a -> PRight (f x (runWitAll a IRight))
    prodAll f = \case
      PLeft    -> WitAll $ \case {}
      PRight x -> WitAll $ \case IRight -> f x

instance Universe (Either j) where
    idecideAny f = \case
      SLeft  _ -> Disproved $ \case WitAny i _ -> case i of {}
      SRight x -> case f IRight x of
        Proved p    -> Proved $ WitAny IRight p
        Disproved v -> Disproved $ \case
          WitAny IRight p -> v p

    idecideAll f = \case
      SLeft  _ -> Proved $ WitAll $ \case {}
      SRight x -> case f IRight x of
        Proved p    -> Proved $ WitAll $ \case IRight -> p
        Disproved v -> Disproved $ \a -> v $ runWitAll a IRight

-- | Witness an item in a type-level 'NonEmpty' by either indicating that
-- it is the "head", or by providing an index in the "tail".
data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

deriving instance Show (NEIndex as a)

instance (SingI (as :: NonEmpty k), SDecide k) => Decidable (TyPred (NEIndex as)) where
    decide x = withSingI x $ pickElem

-- | Kind-indexed singleton for 'NEIndex'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper
-- 'SNEIndex'', which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SNEIndex as a :: NEIndex as a -> Type where
    SNEHead :: SNEIndex (a ':| as) a 'NEHead
    SNETail :: SIndex as a i -> SNEIndex (b ':| as) a ('NETail i)

deriving instance Show (SNEIndex as a i)

newtype instance Sing (i :: NEIndex as a) where
    SNEIndex' :: SNEIndex as a i -> Sing i

instance SingI 'NEHead where
    sing = SNEIndex' SNEHead

instance SingI i => SingI ('NETail i) where
    sing = case sing of
      SIndex' i -> SNEIndex' (SNETail i)

instance SingKind (NEIndex as a) where
    type Demote (NEIndex as a) = NEIndex as a
    fromSing = \case
      SNEIndex' SNEHead     -> NEHead
      SNEIndex' (SNETail i) -> NETail $ fromSing (SIndex' i)
    toSing = \case
      NEHead   -> SomeSing (SNEIndex' SNEHead)
      NETail i -> withSomeSing i $ \case
        SIndex' j -> SomeSing (SNEIndex' (SNETail j))

instance SDecide (NEIndex as a) where
    (%~) = \case
      SNEIndex' SNEHead -> \case
        SNEIndex' SNEHead     -> Proved Refl
        SNEIndex' (SNETail _) -> Disproved $ \case {}
      SNEIndex' (SNETail i) -> \case
        SNEIndex' SNEHead -> Disproved $ \case {}
        SNEIndex' (SNETail j) -> case SIndex' i %~ SIndex' j of
          Proved Refl -> Proved Refl
          Disproved v -> Disproved $ \case Refl -> v Refl

data NERec :: (k -> Type) -> NonEmpty k -> Type where
    (:&|) :: f a -> Rec f as -> NERec f (a ':| as)
infixr 5 :&|

deriving instance (Show (f a), V.RMap as, V.ReifyConstraint Show f as, V.RecordToList as) => Show (NERec f (a ':| as))

type instance Elem NonEmpty = NEIndex
type instance Prod NonEmpty = NERec

instance Provable (TyPred (NERec Sing)) where
    prove = singProd

instance HasProd NonEmpty where
    singProd (x NE.:%| xs) = x :&| singProd xs
    withIndices (x :&| xs) =
          (NEHead :*: x)
      :&| mapProd (\(i :*: y) -> NETail i :*: y) (withIndices xs)
    traverseProd f (x :&| xs) =
        (:&|) <$> f x <*> traverseProd f xs
    zipWithProd f (x :&| xs) (y :&| ys) = f x y :&| zipWithProd f xs ys
    ixProd = \case
      NEHead -> \f -> \case
        x :&| xs -> (:&| xs) <$> f x
      NETail i -> \f -> \case
        x :&| xs -> (x :&|) <$> ixProd i f xs
    allProd
        :: forall p g. ()
        => (forall a. Sing a -> p @@ a -> g a)
        -> All NonEmpty p --> TyPred (Prod NonEmpty g)
    allProd f (x NE.:%| xs) a =
          f x (runWitAll a NEHead)
      :&| allProd @[] @p f xs (WitAll (runWitAll a . NETail))
    prodAll
        :: forall p g as. ()
        => (forall a. g a -> p @@ a)
        -> Prod NonEmpty g as
        -> All NonEmpty p @@ as
    prodAll f (x :&| xs) = WitAll $ \case
        NEHead   -> f x
        NETail i -> runWitAll (prodAll @[] @p f xs) i

instance Universe NonEmpty where
    idecideAny
        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any NonEmpty p @@ as)
    idecideAny f (x NE.:%| xs) = case f NEHead x of
      Proved p    -> Proved $ WitAny NEHead p
      Disproved v -> case idecideAny @[] @_ @p (f . NETail) xs of
        Proved (WitAny i p) -> Proved $ WitAny (NETail i) p
        Disproved vs     -> Disproved $ \case
          WitAny i p -> case i of
            NEHead    -> v p
            NETail i' -> vs (WitAny i' p)

    idecideAll
        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All NonEmpty p @@ as)
    idecideAll f (x NE.:%| xs) = case f NEHead x of
      Proved p -> case idecideAll @[] @_ @p (f . NETail) xs of
        Proved ps -> Proved $ WitAll $ \case
          NEHead   -> p
          NETail i -> runWitAll ps i
        Disproved v -> Disproved $ \a -> v $ WitAll (runWitAll a . NETail)
      Disproved v -> Disproved $ \a -> v $ runWitAll a NEHead

-- | Test if two indices point to the same item in a non-empty list.
--
-- We have to return a 'Maybe' here instead of a 'Decision', because it
-- might be the case that the same item might be duplicated in a list.
-- Therefore, even if two indices are different, we cannot prove that the
-- values they point to are different.
--
-- @since 0.1.5.1
sameNEIndexVal
    :: NEIndex as a
    -> NEIndex as b
    -> Maybe (a :~: b)
sameNEIndexVal = \case
    NEHead -> \case
      NEHead   -> Just Refl
      NETail _ -> Nothing
    NETail i -> \case
      NEHead   -> Nothing
      NETail j -> sameIndexVal i j <&> \case Refl -> Refl

-- | Trivially witness an item in the second field of a type-level tuple.
data ISnd :: (j, k) -> k -> Type where
    ISnd :: ISnd '(a, b) b

deriving instance Show (ISnd as a)

-- TODO: does this interfere with NonNull stuff?
instance (SingI (as :: (j, k)), SDecide k) => Decidable (TyPred (ISnd as)) where
    decide x = withSingI x $ pickElem

-- | Kind-indexed singleton for 'ISnd'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SISnd'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SISnd as a :: ISnd as a -> Type where
    SISnd :: SISnd '(a, b) b 'ISnd

deriving instance Show (SISnd as a i)

newtype instance Sing (i :: ISnd as a) where
    SISnd' :: SISnd as a i -> Sing i

instance SingI 'ISnd where
    sing = SISnd' SISnd

instance SingKind (ISnd as a) where
    type Demote (ISnd as a) = ISnd as a
    fromSing (SISnd' SISnd) = ISnd
    toSing ISnd = SomeSing (SISnd' SISnd)

instance SDecide (ISnd as a) where
    SISnd' SISnd %~ SISnd' SISnd = Proved Refl

data PTup :: (k -> Type) -> (j, k) -> Type where
    PSnd :: f a -> PTup f '(w, a)

deriving instance Show (f a) => Show (PTup f '(w, a))

instance Provable (TyPred (PTup Sing)) where
    prove = singProd

type instance Elem ((,) j) = ISnd
type instance Prod ((,) j) = PTup

instance HasProd ((,) j) where
    singProd (STuple2 _ x) = PSnd x
    withIndices (PSnd x) = PSnd (ISnd :*: x)
    traverseProd f (PSnd x) = PSnd <$> f x
    zipWithProd f (PSnd x) (PSnd y) = PSnd (f x y)
    ixProd ISnd f (PSnd x) = PSnd <$> f x
    allProd f (STuple2 _ x) a = PSnd $ f x (runWitAll a ISnd)
    prodAll f (PSnd x) = WitAll $ \case ISnd -> f x

instance Universe ((,) j) where
    idecideAny f (STuple2 _ x) = case f ISnd x of
      Proved p    -> Proved $ WitAny ISnd p
      Disproved v -> Disproved $ \case WitAny ISnd p -> v p

    idecideAll f (STuple2 _ x) = case f ISnd x of
      Proved p    -> Proved $ WitAll $ \case ISnd -> p
      Disproved v -> Disproved $ \a -> v $ runWitAll a ISnd

-- | There are no items of type @a@ in a @'Proxy' a@.
--
-- @since 0.1.3.0
data IProxy :: Proxy k -> k -> Type

deriving instance Show (IProxy 'Proxy a)

instance (SingI (as :: Proxy k), SDecide k) => Decidable (TyPred (IProxy as)) where
    decide x = withSingI x $ pickElem

instance Provable (TyPred (PProxy Sing)) where
    prove = singProd

instance Provable (Not (TyPred (IProxy 'Proxy))) where
    prove _ = \case {}

-- | Kind-indexed singleton for 'IProxy'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIProxy'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIProxy as a :: IProxy as a -> Type

deriving instance Show (SIProxy as a i)

newtype instance Sing (i :: IProxy as a) where
    SIProxy' :: SIProxy as a i -> Sing i

instance SingKind (IProxy as a) where
    type Demote (IProxy as a) = IProxy as a
    fromSing (SIProxy' i) = case i of {}
    toSing = \case {}

instance SDecide (IProxy as a) where
    SIProxy' i %~ SIProxy' _ = Proved $ case i of {}

data PProxy :: (k -> Type) -> Proxy k -> Type where
    PProxy :: PProxy f 'Proxy

deriving instance Show (PProxy f 'Proxy)

type instance Elem Proxy = IProxy
type instance Prod Proxy = PProxy

instance HasProd Proxy where
    singProd _ = unsafeCoerce PProxy    -- no SProxy yet in singletons
    withIndices PProxy = PProxy
    traverseProd _ PProxy = pure PProxy
    zipWithProd _ PProxy PProxy = PProxy
    ixProd i = lens (case i of {}) (case i of {})
    allProd _ _ _ = unsafeCoerce PProxy     -- no SProxy yet
    prodAll _ PProxy = WitAll $ \case {}

-- | The null universe
instance Universe Proxy where
    idecideAny _ _ = Disproved $ \case
        WitAny i _ -> case i of {}
    idecideAll _ _ = Proved $ WitAll $ \case {}

-- | Trivially witness the item held in an 'Identity'.
--
-- @since 0.1.3.0
data IIdentity :: Identity k -> k -> Type where
    IId :: IIdentity ('Identity x) x

deriving instance Show (IIdentity as a)

instance (SingI (as :: Identity k), SDecide k) => Decidable (TyPred (IIdentity as)) where
    decide x = withSingI x $ pickElem

-- | Kind-indexed singleton for 'IIdentity'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIIdentity'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIIdentity as a :: IIdentity as a -> Type where
    SIId :: SIIdentity ('Identity a) a 'IId

deriving instance Show (SIIdentity as a i)

newtype instance Sing (i :: IIdentity as a) where
    SIIdentity' :: SIIdentity as a i -> Sing i

instance SingI 'IId where
    sing = SIIdentity' SIId

instance SingKind (IIdentity as a) where
    type Demote (IIdentity as a) = IIdentity as a
    fromSing (SIIdentity' SIId) = IId
    toSing IId = SomeSing (SIIdentity' SIId)

instance SDecide (IIdentity as a) where
    SIIdentity' SIId %~ SIIdentity' SIId = Proved Refl

instance Provable (TyPred (PIdentity Sing)) where
    prove = singProd

data PIdentity :: (k -> Type) -> Identity k -> Type where
    PId :: f a -> PIdentity f ('Identity a)

deriving instance Show (f a) => Show (PIdentity f ('Identity a))

type instance Elem Identity = IIdentity
type instance Prod Identity = PIdentity

instance HasProd Identity where
    singProd (SIdentity x) = PId x
    withIndices (PId x) = PId (IId :*: x)
    traverseProd f (PId x) = PId <$> f x
    zipWithProd f (PId x) (PId y) = PId (f x y)
    ixProd IId f (PId x) = PId <$> f x
    allProd f (SIdentity x) a = PId $ f x (runWitAll a IId)
    prodAll f (PId x) = WitAll $ \case IId -> f x

-- | The single-pointed universe.
instance Universe Identity where
    idecideAny f (SIdentity x) = mapDecision (WitAny IId)
                                             (\case WitAny IId p -> p)
                               $ f IId x
    idecideAll f (SIdentity x) = mapDecision (\p -> WitAll $ \case IId -> p)
                                             (`runWitAll` IId)
                               $ f IId x

-- | Compose two Functors.  Is the same as 'Data.Functor.Compose.Compose'
-- and 'GHC.Generics.:.:', except with a singleton and meant to be used at
-- the type level.  Will be redundant if either of the above gets brought
-- into the singletons library.
--
-- Note that because this is a higher-kinded data constructor, there is no
-- 'SingKind'  instance; if you need 'fromSing' and 'toSing', try going
-- through 'Comp' and 'getComp' and 'SComp' and 'sGetComp'.
--
-- Note that 'Identity' acts as an identity.
--
-- @since 0.1.2.0
data (f :.: g) a = Comp { getComp :: f (g a) }
    deriving (Show, Eq, Ord, Functor, Foldable, Typeable, Generic)
deriving instance (Traversable f, Traversable g) => Traversable (f :.: g)

data instance Sing (k :: (f :.: g) a) where
    SComp :: Sing x -> Sing ('Comp x)

-- | 'getComp' lifted to the type level
--
-- @since 0.1.2.0
type family GetComp c where
    GetComp ('Comp a) = a

-- | Singletonized witness for 'GetComp'
--
-- @since 0.1.2.0
sGetComp :: Sing a -> Sing (GetComp a)
sGetComp (SComp x) = x

instance SingI ass => SingI ('Comp ass) where
    sing = SComp sing

data GetCompSym0 :: (f :.: g) k ~> f (g k)
type instance Apply GetCompSym0 ('Comp ass) = ass
type GetCompSym1 a = GetComp a

-- instance forall f g a f' g' a'. (SingKind (f (g a)), Demote (f (g a)) ~ f' (g' a')) => SingKind ((f :.: g) a) where
--     type Demote ((f :.: g) a) = (:.:) f' g' a'

-- | A pair of indices allows you to index into a nested structure.
--
-- @since 0.1.2.0
data CompElem :: (f :.: g) k -> k -> Type where
    (:?) :: Elem f ass as
         -> Elem g as  a
         -> CompElem ('Comp ass) a

-- deriving instance ((forall as. Show (Elem f ass as)), (forall as. Show (Elem g as a)))
--     => Show (CompElem ('Comp ass :: (f :.: g) k) a)

data CompProd :: (k -> Type) -> (p :.: q) k -> Type where
    CompProd :: Prod p (Prod q f) as -> CompProd f ('Comp as)

deriving instance Show (Prod p (Prod q f) as) => Show (CompProd f ('Comp as))

_CompProd :: Lens (CompProd f ('Comp as)) (CompProd f' ('Comp as'))
                  (Prod p (Prod q f) as)  (Prod p' (Prod q' f') as')
_CompProd f (CompProd xs) = CompProd <$> f xs

instance (HasProd p, HasProd q) => Provable (TyPred (CompProd Sing :: (p :.: q) Type -> Type)) where
    prove = singProd

type instance Elem (f :.: g) = CompElem
type instance Prod (f :.: g) = CompProd

instance (HasProd f, HasProd g) => HasProd (f :.: g) where
    singProd (SComp x) = CompProd . mapProd singProd $ singProd x
    withIndices (CompProd xs) = CompProd
                              . imapProd (\i -> imapProd (\j x -> ((i :? j) :*: x)))
                              $ xs
    traverseProd f (CompProd xs) = CompProd <$> traverseProd (traverseProd f) xs
    zipWithProd f (CompProd xs) (CompProd ys) =
      CompProd $ zipWithProd (zipWithProd f) xs ys
    ixProd (i :? j) = _CompProd . ixProd i . ixProd j
    prodAll _ = error "Unimplemented"
    allProd _ = error "Unimplemented"

instance (Universe f, Universe g) => Universe (f :.: g) where
    idecideAny
        :: forall k (p :: k ~> Type) (ass :: (f :.: g) k). ()
        => (forall a. Elem (f :.: g) ass a -> Sing a -> Decision (p @@ a))
        -> Sing ass
        -> Decision (Any (f :.: g) p @@ ass)
    idecideAny f (SComp xss)
        = mapDecision anyComp compAny
        . idecideAny @f @_ @(Any g p) go
        $ xss
      where
        go  :: Elem f (GetComp ass) as
            -> Sing as
            -> Decision (Any g p @@ as)
        go i = idecideAny $ \j -> f (i :? j)

    idecideAll
        :: forall k (p :: k ~> Type) (ass :: (f :.: g) k). ()
        => (forall a. Elem (f :.: g) ass a -> Sing a -> Decision (p @@ a))
        -> Sing ass
        -> Decision (All (f :.: g) p @@ ass)
    idecideAll f (SComp xss)
        = mapDecision allComp compAll
        . idecideAll @f @_ @(All g p) go
        $ xss
      where
        go  :: Elem f (GetComp ass) as
            -> Sing as
            -> Decision (All g p @@ as)
        go i = idecideAll $ \j -> f (i :? j)

-- | Turn a composition of 'Any' into an 'Any' of a composition.
--
-- @since 0.1.2.0
anyComp :: Any f (Any g p) @@ as -> Any (f :.: g) p @@ 'Comp as
anyComp (WitAny i (WitAny j p)) = WitAny (i :? j) p

-- | Turn an 'Any' of a composition into a composition of 'Any'.
--
-- @since 0.1.2.0
compAny :: Any (f :.: g) p @@ 'Comp as -> Any f (Any g p) @@ as
compAny (WitAny (i :? j) p) = WitAny i (WitAny j p)

-- | Turn a composition of 'All' into an 'All' of a composition.
--
-- @since 0.1.2.0
allComp :: All f (All g p) @@ as -> All (f :.: g) p @@ 'Comp as
allComp a = WitAll $ \(i :? j) -> runWitAll (runWitAll a i) j

-- | Turn an 'All' of a composition into a composition of 'All'.
--
-- @since 0.1.2.0
compAll :: All (f :.: g) p @@ 'Comp as -> All f (All g p) @@ as
compAll a = WitAll $ \i -> WitAll $ \j -> runWitAll a (i :? j)

-- | Disjoint union of two Functors.  Is the same as 'Data.Functor.Sum.Sum'
-- and 'GHC.Generics.:+:', except with a singleton and meant to be used at
-- the type level.  Will be redundant if either of the above gets brought
-- into the singletons library.
--
-- Note that because this is a higher-kinded data constructor, there is no
-- 'SingKind'  instance; if you need 'fromSing' and 'toSing', consider
-- manually pattern matching.
--
-- Note that 'Proxy' acts as an identity.
--
-- @since 0.1.3.0
data (f :+: g) a = InL (f a)
                 | InR (g a)
    deriving (Show, Eq, Ord, Functor, Foldable, Typeable, Generic)
deriving instance (Traversable f, Traversable g) => Traversable (f :+: g)

data instance Sing (k :: (f :+: g) a) where
    SInL :: Sing x -> Sing ('InL x)
    SInR :: Sing y -> Sing ('InR y)

type family FromL s where
    FromL ('InL a) = a

-- | Index into a disjoint union by providing an index into one of the two
-- possible options.
--
-- @since 0.1.3.0
data SumElem :: (f :+: g) k -> k -> Type where
    IInL :: Elem f as a -> SumElem ('InL as) a
    IInR :: Elem f bs b -> SumElem ('InR bs) b

data PSum :: (k -> Type) -> (p :+: q) k -> Type where
    PInL :: Prod p f a -> PSum f ('InL a)
    PInR :: Prod q f a -> PSum f ('InR a)

_PInL :: Lens (PSum f ('InL a)) (PSum f ('InL a'))
              (Prod p f a)      (Prod p' f a')
_PInL f (PInL x) = PInL <$> f x

_PInR :: Lens (PSum f ('InR b)) (PSum f ('InR b'))
              (Prod q f b)      (Prod q' f b')
_PInR f (PInR y) = PInR <$> f y

instance (HasProd p, HasProd q) => Provable (TyPred (PSum Sing :: (p :+: q) Type -> Type)) where
    prove = singProd

type instance Elem (f :+: g) = SumElem
type instance Prod (f :+: g) = PSum

instance (HasProd f, HasProd g) => HasProd (f :+: g) where
    singProd = \case
      SInL xs -> PInL $ singProd xs
      SInR ys -> PInR $ singProd ys
    withIndices = \case
      PInL xs -> PInL $ imapProd (\i x -> (IInL i :*: x)) xs
      PInR ys -> PInR $ imapProd (\i y -> (IInR i :*: y)) ys
    traverseProd f = \case
      PInL xs -> PInL <$> traverseProd f xs
      PInR ys -> PInR <$> traverseProd f ys
    zipWithProd f = \case
      PInL xs -> \case
        PInL xs' -> PInL (zipWithProd f xs xs')
      PInR ys -> \case
        PInR ys' -> PInR (zipWithProd f ys ys')
    ixProd = \case
      IInL i -> _PInL . ixProd i
      IInR j -> _PInR . ixProd j
    allProd _ = error "Unimplemented"
    prodAll _ = error "Unimplemented"

instance (Universe f, Universe g) => Universe (f :+: g) where
    idecideAny
        :: forall k (p :: k ~> Type) (abs :: (f :+: g) k). ()
        => (forall ab. Elem (f :+: g) abs ab -> Sing ab -> Decision (p @@ ab))
        -> Sing abs
        -> Decision (Any (f :+: g) p @@ abs)
    idecideAny f = \case
      SInL xs -> mapDecision anySumL sumLAny
               $ idecideAny @f @_ @p (f . IInL) xs
      SInR ys -> mapDecision anySumR sumRAny
               $ idecideAny @g @_ @p (f . IInR) ys

    idecideAll
        :: forall k (p :: k ~> Type) (abs :: (f :+: g) k). ()
        => (forall ab. Elem (f :+: g) abs ab -> Sing ab -> Decision (p @@ ab))
        -> Sing abs
        -> Decision (All (f :+: g) p @@ abs)
    idecideAll f = \case
      SInL xs -> mapDecision allSumL sumLAll
               $ idecideAll @f @_ @p (f . IInL) xs
      SInR xs -> mapDecision allSumR sumRAll
               $ idecideAll @g @_ @p (f . IInR) xs

-- | Turn an 'Any' of @f@ into an 'Any' of @f ':+:' g@.
anySumL :: Any f p @@ as -> Any (f :+: g) p @@ 'InL as
anySumL (WitAny i x) = WitAny (IInL i) x

-- | Turn an 'Any' of @g@ into an 'Any' of @f ':+:' g@.
anySumR :: Any g p @@ bs -> Any (f :+: g) p @@ 'InR bs
anySumR (WitAny j y) = WitAny (IInR j) y

-- | Turn an 'Any' of @f ':+:' g@ into an 'Any' of @f@.
sumLAny :: Any (f :+: g) p @@ 'InL as -> Any f p @@ as
sumLAny (WitAny (IInL i) x) = WitAny i x

-- | Turn an 'Any' of @f ':+:' g@ into an 'Any' of @g@.
sumRAny :: Any (f :+: g) p @@ 'InR bs -> Any g p @@ bs
sumRAny (WitAny (IInR j) y) = WitAny j y

-- | Turn an 'All' of @f@ into an 'All' of @f ':+:' g@.
allSumL :: All f p @@ as -> All (f :+: g) p @@ 'InL as
allSumL a = WitAll $ \case IInL i -> runWitAll a i

-- | Turn an 'All' of @g@ into an 'All' of @f ':+:' g@.
allSumR :: All g p @@ bs -> All (f :+: g) p @@ 'InR bs
allSumR a = WitAll $ \case IInR j -> runWitAll a j

-- | Turn an 'All' of @f ':+:' g@ into an 'All' of @f@.
sumLAll :: All (f :+: g) p @@ 'InL as -> All f p @@ as
sumLAll a = WitAll $ runWitAll a . IInL

-- | Turn an 'All' of @f ':+:' g@ into an 'All' of @g@.
sumRAll :: All (f :+: g) p @@ 'InR bs -> All g p @@ bs
sumRAll a = WitAll $ runWitAll a . IInR

