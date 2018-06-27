{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -Wno-orphans     #-}

module Data.Type.Universe (
    Universe(..), Elem(..), genAll, select, splitSing, foldMapUni
  , decideAny', decideAll', genAllA', genAll', foldMapUni'
  , pickElem
  -- * Membership witnesses
  ) where

import           Control.Applicative
import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty                    (NonEmpty(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding        (Any, All, Snd, Elem, ElemSym0, ElemSym1, ElemSym2)
import           Data.Type.Elem.Internal
import           Prelude hiding                        (any, all)
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

-- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- p as@.  Basically witnesses the definition of 'All'.
genAll
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> p @@ a)            -- ^ always-true predicate on value
    -> (Sing as -> All f p as)                                  -- ^ always-true predicate on collection
genAll f = runIdentity . genAllA (\i -> Identity . f i)

-- | Extract the item from the container witnessed by the 'Elem'
select
    :: forall f as a. Universe f
    => Elem f as a        -- ^ Witness
    -> Sing as            -- ^ Collection
    -> Sing a
select i = (`runAll` i) . splitSing

-- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
splitSing
    :: forall f (as :: f k). Universe f
    => Sing as
    -> All f (TyCon1 Sing) as
splitSing = genAll @f @_ @(TyCon1 Sing) (\_ x -> x)

-- | 'decideAny', but without the membership witness.
decideAny'
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Sing a -> Decision (p @@ a))   -- ^ predicate on value
    -> (Sing as -> Decision (Any f p as))          -- ^ predicate on collection
decideAny' f = decideAny (const f)

-- | 'decideAll', but without the membership witness.
decideAll'
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Sing a -> Decision (p @@ a))   -- ^ predicate on value
    -> (Sing as -> Decision (All f p as))          -- ^ predicate on collection
decideAll' f = decideAll (const f)

-- | 'genAllA', but without the membership witness.
genAllA'
    :: forall k (p :: k ~> Type) (as :: f k) h. (Universe f, Applicative h)
    => (forall a. Sing a -> h (p @@ a))        -- ^ predicate on value in context
    -> (Sing as -> h (All f p as))               -- ^ predicate on collection in context
genAllA' f = genAllA (const f)

-- | 'genAll', but without the membership witness.
genAll'
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Sing a -> p @@ a)            -- ^ always-true predicate on value
    -> (Sing as -> All f p as)                   -- ^ always-true predicate on collection
genAll' f = genAll (const f)

-- | Automatically generate a witness for a member, if possible
pickElem
    :: forall f k (as :: f k) a. (Universe f, SingI as, SingI a, SDecide k)
    => Decision (Elem f as a)
pickElem = case decideAny' @f @_ @(TyCon1 ((:~:) a)) go (sing @_ @as) of
    Proved (Any i Refl) -> Proved i
    Disproved v         -> Disproved $ \i -> v $ Any i Refl
  where
    go :: Sing b -> Decision (a :~: b)
    go = (sing %~)

-- | A 'foldMap' over all items in a collection.
foldMapUni
    :: forall f k (as :: f k) m. (Universe f, SingI as, Monoid m)
    => (forall a. Elem f as a -> Sing a -> m)
    -> Sing as
    -> m
foldMapUni f = getConst . genAllA (\i -> Const . f i)

-- | 'foldMapUni', but without the membership witness.
foldMapUni'
    :: forall f k (as :: f k) m. (Universe f, SingI as, Monoid m)
    => (forall a. Elem f as a -> Sing a -> m)
    -> Sing as
    -> m
foldMapUni' f = getConst . genAllA (\i -> Const . f i)


-- | Witness an item in a type-level list by providing its index.
data instance Elem []  :: [k] -> k -> Type where
    IZ :: Elem [] (a ': as) a
    IS :: Elem [] bs a -> Elem [] (b ': bs) a

deriving instance Show (Elem [] as a)

instance Universe [] where
    decideAny
        :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any [] p as)
    decideAny f = \case
      SNil -> Disproved $ \case
        Any i _ -> case i of {}
      x `SCons` xs -> case f IZ x of
        Proved p    -> Proved $ Any IZ p
        Disproved v -> case decideAny @[] @_ @p (f . IS) xs of
          Proved (Any i p) -> Proved $ Any (IS i) p
          Disproved vs -> Disproved $ \case
            Any IZ     p -> v p
            Any (IS i) p -> vs (Any i p)

    decideAll
        :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Elem [] as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All [] p as)
    decideAll f = \case
      SNil -> Proved $ All $ \case {}
      x `SCons` xs -> case f IZ x of
        Proved p -> case decideAll @[] @_ @p (f . IS) xs of
          Proved a -> Proved $ All $ \case
            IZ   -> p
            IS i -> runAll a i
          Disproved v -> Disproved $ \a -> v $ All (runAll a . IS)
        Disproved v -> Disproved $ \a -> v $ runAll a IZ

    genAllA
        :: forall (p :: k ~> Type) (as :: [k]) h. Applicative h
        => (forall a. Elem [] as a -> Sing a -> h (p @@ a))
        -> Sing as
        -> h (All [] p as)
    genAllA f = \case
        SNil         -> pure $ All $ \case {}
        x `SCons` xs -> go <$> f IZ x <*> genAllA (f . IS) xs
      where
        go :: p @@ b -> All [] p bs -> All [] p (b ': bs)
        go p a = All $ \case
          IZ   -> p
          IS i -> runAll a i

-- | Witness an item in a type-level 'Maybe' by proving the 'Maybe' is
-- 'Just'.
data instance Elem Maybe :: Maybe k -> k -> Type where
    IsJust :: Elem Maybe ('Just a) a

deriving instance Show (Elem Maybe as a)

instance Universe Maybe where
    decideAny f = \case
      SNothing -> Disproved $ \case Any i _ -> case i of {}
      SJust x  -> case f IsJust x of
        Proved p    -> Proved $ Any IsJust p
        Disproved v -> Disproved $ \case
          Any IsJust p -> v p

    decideAll f = \case
      SNothing -> Proved $ All $ \case {}
      SJust x  -> case f IsJust x of
        Proved p    -> Proved $ All $ \case IsJust -> p
        Disproved v -> Disproved $ \a -> v $ runAll a IsJust

    genAllA f = \case
      SNothing -> pure $ All $ \case {}
      SJust x  -> (\p -> All $ \case IsJust -> p) <$> f IsJust x

-- | Witness an item in a type-level @'Either' j@ by proving the 'Either'
-- is 'Right'.
data instance Elem (Either j) :: Either j k -> k -> Type where
    IsRight :: Elem (Either j) ('Right a) a

deriving instance Show (Elem (Either j) as a)

instance Universe (Either j) where
    decideAny f = \case
      SLeft  _ -> Disproved $ \case Any i _ -> case i of {}
      SRight x -> case f IsRight x of
        Proved p    -> Proved $ Any IsRight p
        Disproved v -> Disproved $ \case
          Any IsRight p -> v p

    decideAll f = \case
      SLeft  _ -> Proved $ All $ \case {}
      SRight x -> case f IsRight x of
        Proved p    -> Proved $ All $ \case IsRight -> p
        Disproved v -> Disproved $ \a -> v $ runAll a IsRight

    genAllA f = \case
      SLeft  _ -> pure $ All $ \case {}
      SRight x -> (\p -> All $ \case IsRight -> p) <$> f IsRight x

-- | Witness an item in a type-level 'NonEmpty' by either indicating that
-- it is the "head", or by providing an index in the "tail".
data instance Elem NonEmpty :: NonEmpty k -> k -> Type where
    NEHead :: Elem NonEmpty (a ':| as) a
    NETail :: Elem [] as a -> Elem NonEmpty (b ':| as) a

deriving instance Show (Elem NonEmpty as a)

instance Universe NonEmpty where
    decideAny
        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any NonEmpty p as)
    decideAny f (x NE.:%| xs) = case f NEHead x of
      Proved p    -> Proved $ Any NEHead p
      Disproved v -> case decideAny @[] @_ @p (f . NETail) xs of
        Proved (Any i p) -> Proved $ Any (NETail i) p
        Disproved vs     -> Disproved $ \case
          Any i p -> case i of
            NEHead    -> v p
            NETail i' -> vs (Any i' p)

    decideAll
        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Elem NonEmpty as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All NonEmpty p as)
    decideAll f (x NE.:%| xs) = case f NEHead x of
      Proved p -> case decideAll @[] @_ @p (f . NETail) xs of
        Proved ps -> Proved $ All $ \case
          NEHead   -> p
          NETail i -> runAll ps i
        Disproved v -> Disproved $ \a -> v $ All (runAll a . NETail)
      Disproved v -> Disproved $ \a -> v $ runAll a NEHead

    genAllA
        :: forall (p :: k ~> Type) (as :: NonEmpty k) h. Applicative h
        => (forall a. Elem NonEmpty as a -> Sing a -> h (p @@ a))
        -> Sing as
        -> h (All NonEmpty p as)
    genAllA f (x NE.:%| xs) = go <$> f NEHead x <*> genAllA @[] @_ @p (f . NETail) xs
      where
        go :: p @@ b -> All [] p bs -> All NonEmpty p (b ':| bs)
        go p ps = All $ \case
          NEHead   -> p
          NETail i -> runAll ps i

-- | Trivially witness an item in the second field of a type-level tuple.
data instance Elem ((,) j) :: (j, k) -> k -> Type where
    Snd :: Elem ((,) j) '(a, b) b

deriving instance Show (Elem ((,) j) as a)

instance Universe ((,) j) where
    decideAny f (STuple2 _ x) = case f Snd x of
      Proved p    -> Proved $ Any Snd p
      Disproved v -> Disproved $ \case Any Snd p -> v p

    decideAll f (STuple2 _ x) = case f Snd x of
      Proved p    -> Proved $ All $ \case Snd -> p
      Disproved v -> Disproved $ \a -> v $ runAll a Snd

    genAllA f (STuple2 _ x) = (\p -> All $ \case Snd -> p) <$> f Snd x
