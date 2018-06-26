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
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Elem (
    Elem, Universe(..), genAll, select
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
import           Prelude hiding                        (any, all)
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

-- | A witness for membership of a given item in a type-level collection
type family Elem (f :: Type -> Type) :: f k -> k -> Type

-- | An @'Any' p as@ is a witness that, for at least one item @a@ in the
-- type-level collection @as@, the predicate @p a@ is true.
data Any :: (k ~> Type) -> f k -> Type where
    Any :: Elem f as a -> p @@ a -> Any p as

-- | An @'All' p as@ is a witness that, the predicate @p a@ is true for all
-- items @a@ in the type-level collection @as@.
newtype All p (as :: f k) = All { runAll :: forall a. Elem f as a -> p @@ a }

-- | Typeclass for a type-level container that you can quantify or lift
-- type-level predicates over.
class Universe (f :: Type -> Type) where

    -- | You should read this type as:
    --
    -- @
    -- 'decideAny' :: ('Sing' a  -> 'Decision' (p a)    )
    --           -> (Sing as -> Decision (Any p as)
    -- @
    --
    -- It lifts a predicate @p@ on an individual @a@ into a predicate that
    -- on a collection @as@ that is true if and only if /any/ item in @as@
    -- satisfies the original predicate.
    --
    -- That is, it turns a predicate of kind @k ~> Type@ into a predicate
    -- of kind @f k ~> Type@.
    --
    -- Essentially tests existential quantification.
    decideAny
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)

    -- | You should read this type as:
    --
    -- @
    -- 'decideAll' :: ('Sing' a  -> 'Decision' (p a)    )
    --           -> ('Sing' as -> 'Decision' (All p as)
    -- @
    --
    -- It lifts a predicate @p@ on an individual @a@ into a predicate that
    -- on a collection @as@ that is true if and only if /all/ items in @as@
    -- satisfies the original predicate.
    --
    -- That is, it turns a predicate of kind @k ~> Type@ into a predicate
    -- of kind @f k ~> Type@.
    --
    -- Essentially tests universal quantification.
    decideAll
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)

    -- | If @p a@ is true for all values @a@ in @as@ under some
    -- (Applicative) context @h@, then you can create an @'All' p as@ under
    -- that Applicative context @h@.
    --
    -- Can be useful with 'Identity' (which is basically unwrapping and
    -- wrapping 'All'), or with 'Maybe' (which can express predicates that
    -- are either provably true or not provably false).
    genAllA
        :: forall k (p :: k ~> Type) (as :: f k) h. Applicative h
        => (forall a. Elem f as a -> Sing a -> h (p @@ a))
        -> Sing as
        -> h (All p as)

-- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- p as@.  Basically witnesses the definition of 'All'.
genAll
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> p @@ a)
    -> Sing as
    -> All p as
genAll f = runIdentity . genAllA (\i -> Identity . f i)

-- | Extract the item from the container witnessed by the 'Elem'
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
-- @h@ might be something like, say, 'Maybe', to give predicate that is
-- either provably true or unprovably false.
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

-- | Witness an item in a type-level list by providing its index.
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

-- | Witness an item in a type-level 'Maybe' by proving the 'Maybe' is
-- 'Just'.
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

-- | Witness an item in a type-level 'NonEmpty' by either indicating that
-- it is the "head", or by providing an index in the "tail".
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
      
-- | Trivially witness an item in the second field of a type-level tuple.
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
