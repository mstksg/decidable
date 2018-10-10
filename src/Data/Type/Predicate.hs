{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Type.Predicate (
    -- * Predicates
    Predicate, Wit(..)
    -- ** Construct Predicates
  , TyPred, Evident, EqualTo, BoolPred
    -- ** Manipulate predicates
  , PMap
  , type Not, decideNot
  , type (&&&), decideAnd
  , type (|||), decideOr
  , type (^^^), decideXor
    -- * Provable Predicates
  , Prove, type (-->), type (-->#)
  , Provable(..)
  , TFunctor(..)
  , compImpl
    -- * Decidable Predicates
  , Decide, type (-?>), type (-?>#)
  , Decidable(..)
  , DFunctor(..)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Not)

-- | A type-level predicate in Haskell.  We say that the predicate @P ::
-- 'Predicate k'@ is true/satisfied by input @x :: k@ if there exists a value of
-- type @P @@ x@, and that it false/disproved if such a value cannot exist.
type Predicate k = k ~> Type

-- | Convert a normal '->' type constructor into a 'Predicate'.
--
-- @
-- 'TyPred' :: (k -> 'Type') -> 'Predicate' k
-- @
type TyPred = (TyCon1 :: (k -> Type) -> Predicate k)

-- | The always-true predicate.
--
-- @
-- 'Evident' :: 'Predicate' k
-- @
type Evident = (TyPred Sing :: Predicate k)

type EqualTo a = TyCon1 ((:~:) a)

-- | Convert a tradtional @k ~> 'Bool'@ predicate into a 'Predicate'.
--
-- @
-- 'BoolPred' :: (k ~> Bool) -> Predicate k
-- @
type BoolPred (p :: k ~> Bool) = (EqualTo 'True .@#@$$$ p :: Predicate k)

-- | Pre-compose a function to a predicate
--
-- @
-- 'PMap' :: (k ~> j) -> 'Predicate' j -> Predicate k
-- @
type PMap (f :: k ~> j) (p :: Predicate j) = (p .@#@$$$ f :: Predicate k)

-- | A @'Wit' p a@ is a value of type @p @@ a@ --- that is, it is a proof
-- or witness that @p@ is satisfied for @a@.
newtype Wit p a = Wit { getWit :: p @@ a }

-- | A decision function for predicate @p@.  See 'Decidable' for more
-- information.
type Decide p = forall a. Sing a -> Decision (p @@ a)

-- | Like implication '-->', but knowing @p @@ a@ can only let us decidably
-- prove @q @@ a@ is true or false.
type p -?> q = forall a. Sing a -> p @@ a -> Decision (q @@ a)

-- | Like '-?>', but only in a specific context @h@.
type (p -?># q) h = forall a. Sing a -> p @@ a -> h (Decision (q @@ a))

-- | A proving function for predicate @p@.  See 'Provable' for more
-- information.
type Prove p = forall a. Sing a -> p @@ a

-- | We say that @p@ implies @q@ (@p '-->' q@) if, given @p @@ a@, we can
-- always prove @q @@ a@.
type p --> q = forall a. Sing a -> p @@ a -> q @@ a

-- | This is implication '-->#', but only in a specific context @h@.
type (p --># q) h = forall a. Sing a -> p @@ a -> h (q @@ a)

infixr 2 -?>
infixr 2 -?>#
infixr 2 -->
infixr 2 -->#

-- | A typeclass for decidable predicates.
--
-- A predicate is decidable if, given any input @a@, you can either prove
-- or disprove @p @@ a@.  A @'Decision' (p @@ a)@ is a data type that has
-- a branch @p @@ a@ and @'Refuted' (p @@ a)@.
--
-- This typeclass associates a canonical decision function for every
-- decidable predicate.
--
-- It confers two main advatnages:
--
--     1. The decision function for every predicate is available via the
--     same name
--
--     2. We can write 'Decidable' instances for polymorphic predicate
--     transformers (predicates parameterized on other predicates) easily,
--     by refering to 'Decidable' instances of the transformed predicates.
class Decidable p where
    -- | The canonical decision function for predicate @p@.
    --
    -- Note that 'decide' is ambiguously typed, so you /always/ need to call by
    -- specifying the predicate you want to prove using TypeApplications
    -- syntax:
    --
    -- @
    -- 'decide' \@MyPredicate
    -- @
    decide :: Decide p

    default decide :: Provable p => Decide p
    decide = Proved . prove @p

-- | A typeclass for provable predicates.
--
-- A predicate is provable if, given any input @a@, you can generate
-- a proof of @p @@ a@.
--
-- This typeclass associates a canonical proof function for every provable
-- predicate.
--
-- It confers two main advatnages:
--
--     1. The proof function for every predicate is available via the same
--     name
--
--     2. We can write 'Provable' instances for polymorphic predicate
--     transformers (predicates parameterized on other predicates) easily,
--     by refering to 'Provable' instances of the transformed predicates.
class Decidable p => Provable p where
    -- | The canonical proving function for predicate @p@.
    --
    -- Note that 'prove' is ambiguously typed, so you /always/ need to call
    -- by specifying the predicate you want to prove using TypeApplications
    -- syntax:
    --
    -- @
    -- 'prove' \@MyPredicate
    -- @
    prove :: Prove p

-- | Implicatons @p '-?>' q@ can be lifted "through" a 'DFunctor' into an
-- @f p '-?>' f q@.
class DFunctor f where
    dmap :: forall p q. (p -?> q) -> (f p -?> f q)

-- | Implicatons @p '-->' q@ can be lifted "through" a 'TFunctor' into an
-- @f p '-->' f q@.
class TFunctor f where
    tmap :: forall p q. (p --> q) -> (f p --> f q)

instance (SDecide k, SingI (a :: k)) => Decidable (EqualTo a) where
    decide = (sing %~)

instance Decidable  Evident
instance Provable Evident where
    prove = id

instance (Decidable f, SingI g) => Decidable (f .@#@$$$ g) where
    decide = decide @f . ((sing :: Sing g) @@)

instance (Provable f, SingI g) => Provable (f .@#@$$$ g) where
    prove = prove @f . ((sing :: Sing g) @@)

-- | @'Not' p@ is the predicate that @p@ is not true.
data Not :: (k ~> Type) -> (k ~> Type)
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
data (&&&) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p &&& q) a = (p @@ a, q @@ a)
infixr 3 &&&

instance (Decidable p, Decidable q) => Decidable (p &&& q) where
    decide (x :: Sing a) = decideAnd @p @q @a (decide @p x) (decide @q x)

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
data (|||) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)
infixr 2 |||

instance (Decidable p, Decidable q) => Decidable (p ||| q) where
    decide (x :: Sing a) = decideOr @p @q @a (decide @p x) (decide @q x)

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

-- | Compose two implications.
compImpl
    :: forall p q r. ()
    => p --> q
    -> q --> r
    -> p --> r
compImpl f g s = g s . f s

