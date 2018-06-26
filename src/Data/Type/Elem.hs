{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Elem (
    Universe(..), genAll, select
  , Any(..), All(..), entailAny, entailAnyF, entailAll, entailAllF, decideEntailAll
  , Index(..)
  , IsJust(..)
  , NEIndex(..)
  , Snd(..)
  ) where

import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty                    (NonEmpty(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding        (Any, All, Snd, Elem, ElemSym0, ElemSym1, ElemSym2)
import           Data.Singletons.Prelude.Functor
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding             (Elem)
import           Prelude hiding                        (any, all)
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

type family Elem (f :: Type -> Type) :: f k -> k -> Type

data Any :: (k ~> Type) -> f k -> Type where
    Any :: Elem f as a -> p @@ a -> Any p as

newtype All p (as :: f k) = All { runAll :: forall a. Elem f as a -> p @@ a }

class Universe (f :: Type -> Type) where

    decideAny
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)

    decideAll
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)

    genAllA
        :: forall k (p :: k ~> Type) (as :: f k) h. Applicative h
        => (forall a. Elem f as a -> Sing a -> h (p @@ a))
        -> Sing as
        -> h (All p as)

genAll
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> p @@ a)
    -> Sing as
    -> All p as
genAll f = runIdentity . genAllA (\i -> Identity . f i)

select
    :: forall f as a. Universe f
    => Elem f as a
    -> Sing as
    -> Sing a
select i = (`runAll` i) . genAll @f @_ @(TyCon1 Sing) (\_ x -> x)

-- | If there exists an @a@ s.t. @p a@, and if @p@ implies @q@, then there
-- must exist an @a@ s.t. @q a@.
entailAny
    :: forall f p q (as :: f k). ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)
    -> Any p as
    -> Any q as
entailAny f (Any i x) = Any i (f i x)

-- | If for all @a@ we have @p a@, and if @p@ implies @q@, then for all @a@
-- we must also have @p a@.
entailAll
    :: forall f p q (as ::  f k). ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)
    -> All p as
    -> All q as
entailAll f a = All $ \i -> f i (runAll a i)

-- | If @p@ implies @q@ under some context @h@, and if there exists some
-- @a@ such that @p a@, then there must exist some @a@ such that @p q@
-- under that context @h@.
--
-- @h@ might be something like, say, 'Maybe', to give a "potentially
-- failing" @p a -> 'Maybe' (q a)@ relationship.
--
-- Note that it is not possible to do this with @p a -> 'Decision' (q a)@.
-- This is if the @p a -> 'Decision' (q a)@ implication is false, there
-- it doesn't mean that there is /no/ @a@ such that @q a@, necessarily.
-- There could have been an @a@ where @p@ does not hold, but @q@ does.
entailAnyF
    :: forall h f p q as. Functor h
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))
    -> Any p as
    -> h (Any q as)
entailAnyF f = \case
    Any i x -> Any i <$> f i x

-- | If @p@ implies @q@ under some context @h@, and if we have @p a@ for
-- all @a@, then we must have @q a@ for all @a@ under context @h@.
entailAllF
    :: forall h f p q as. (Universe f, Applicative h, SingI as)
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))
    -> All p as
    -> h (All q as)
entailAllF f a = genAllA (\i _ -> f i (runAll a i)) sing

-- | If we have @p a@ for all @a@, and @p a@ can be used to test for @q a@,
-- then we can test all @a@s for @q a@.
decideEntailAll
    :: forall f p q (as ::  f k). (Universe f, SingI as)
    => (forall a. Elem f as a -> p @@ a -> Decision (q @@ a))
    -> All p as
    -> Decision (All q as)
decideEntailAll f a = decideAll (\i _ -> f i (runAll a i)) sing

data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

type instance Elem [] = Index

instance Universe [] where
    decideAny
        :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Index as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)
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
        => (forall a. Index as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)
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
        -> h (All p as)
    genAllA f = \case
        SNil         -> pure $ All $ \case {}
        x `SCons` xs -> go <$> f IZ x <*> genAllA (f . IS) xs
      where
        go :: p @@ b -> All p bs -> All p (b ': bs)
        go p a = All $ \case
          IZ   -> p
          IS i -> runAll a i

data IsJust :: Maybe k -> k -> Type where
    IsJust :: IsJust ('Just a) a

type instance Elem Maybe = IsJust

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

data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

type instance Elem NonEmpty = NEIndex

instance Universe NonEmpty where
    decideAny
        :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. NEIndex as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)
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
        => (forall a. NEIndex as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)
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
        -> h (All p as)
    genAllA f (x NE.:%| xs) = go <$> f NEHead x <*> genAllA @[] @_ @p (f . NETail) xs
      where
        go :: p @@ b -> All p bs -> All p (b ':| bs)
        go p ps = All $ \case
          NEHead   -> p
          NETail i -> runAll ps i
      
data Snd :: (j, k) -> k -> Type where
    Snd :: Snd '(a, b) b

type instance Elem ((,) j) = Snd

instance Universe ((,) j) where
    decideAny f (STuple2 _ x) = case f Snd x of
      Proved p    -> Proved $ Any Snd p
      Disproved v -> Disproved $ \case Any Snd p -> v p

    decideAll f (STuple2 _ x) = case f Snd x of
      Proved p    -> Proved $ All $ \case Snd -> p
      Disproved v -> Disproved $ \a -> v $ runAll a Snd

    genAllA f (STuple2 _ x) = (\p -> All $ \case Snd -> p) <$> f Snd x
