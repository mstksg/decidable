{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.Predicate
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Combinators for working with type-level predicates, along with
-- typeclasses for canonical proofs and deciding functions.
--
module Data.Type.Predicate (
    -- * Predicates
    Predicate, Wit(..)
    -- ** Construct Predicates
  , TyPred, Evident, EqualTo, BoolPred, Impossible
    -- ** Manipulate predicates
  , PMap, type Not, decideNot
    -- * Provable Predicates
  , Prove, type (-->), type (-->#)
  , Provable(..)
  , Disprovable, disprove
  , ProvableTC, proveTC
  , TFunctor(..)
  , compImpl
    -- * Decidable Predicates
  , Decide, type (-?>), type (-?>#)
  , Decidable(..)
  , DecidableTC, decideTC
  , DFunctor(..)
  -- * Manipulate Decisions
  , Decision(..)
  , flipDecision, mapDecision
  , elimDisproof
  , forgetDisproof, forgetProof, isProved, isDisproved
  , mapRefuted
  ) where

import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Not)
import           Data.Void

-- | A type-level predicate in Haskell.  We say that the predicate @P ::
-- 'Predicate' k@ is true/satisfied by input @x :: k@ if there exists
-- a value of type @P \@\@ x@, and that it false/disproved if such a value
-- cannot exist. (Where '@@' is 'Apply', the singleton library's type-level
-- function application for mathcable functions)
--
-- See 'Provable' and 'Decidable' for more information on how to use, prove
-- and decide these predicates.
--
-- The kind @k ~> 'Type'@ is the kind of "matchable" type-level functions
-- in Haskell.  They are type-level functions that are encoded as dummy
-- type constructors ("defunctionalization symbols") that can be decidedly
-- "matched" on for things like typeclass instances.
--
-- There are two ways to define your own predicates:
--
--     1. Using the predicate combinators and predicate transformers in
--     this library and the /singletons/ library, which let you construct
--     pre-made predicates and sometimes create predicates from other
--     predicates.
--
--     2. Manually creating a data type that acts as a matchable predicate.
--
-- For an example of the latter, we can create the "not p" predicate, which
-- takes a predicate @p@ as input and returns the negation of the
-- predicate:
--
-- @
-- -- First, create the data type with the kind signature you want
-- data Not :: Predicate k -> Predicate k
--
-- -- Then, write the 'Apply' instance, to specify the type of the
-- -- witnesses of that predicate
-- instance 'Apply' (Not p) a = (p '@@' a) -> Void
-- @
--
-- See the source of "Data.Type.Predicate" and "Data.Type.Predicate.Logic"
-- for simple examples of hand-made predicates.  For example, we have the
-- always-true predicate 'Evident':
--
-- @
-- data Evident :: Predicate k
-- instance Apply Evident a = Sing a
-- @
--
-- And the "and" predicate combinator:
--
-- @
-- data (&&&) :: Predicate k -> Predicate k -> Predicate k
-- instance Apply (p &&& q) a = (p '@@' a, q '@@' a)
-- @
--
-- Typically it is recommended to create predicates from the supplied
-- predicate combinators ('TyPred' can be used for any type constructor to
-- turn it into a predicate, for instance) whenever possible.
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

-- | The always-false predicate
--
-- Could also be defined as @'ConstSym1' Void@, but this defintion gives
-- us a free 'Decidable' instance.
--
-- @
-- 'Impossible' :: 'Predicate' k
-- @
type Impossible = (Not Evident :: Predicate k)

-- | @'EqualTo' a@ is a predicate that the input is equal to @a@.
--
-- @
-- 'EqualTo' :: k -> 'Predicate' k
-- @
type EqualTo (a :: k) = (TyPred ((:~:) a) :: Predicate k)

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

-- | A @'Wit' p a@ is a value of type @p \@\@ a@ --- that is, it is a proof
-- or witness that @p@ is satisfied for @a@.
--
-- It essentially turns a @k ~> 'Type'@ ("matchable" @'Predicate' k@) /back
-- into/ a @k -> 'Type'@ predicate.
newtype Wit p a = Wit { getWit :: p @@ a }

-- | A decision function for predicate @p@.  See 'Decidable' for more
-- information.
type Decide p = forall a. Sing a -> Decision (p @@ a)

-- | Like implication '-->', but knowing @p \@\@ a@ can only let us decidably
-- prove @q @@ a@ is true or false.
type p -?> q = forall a. Sing a -> p @@ a -> Decision (q @@ a)

-- | Like '-?>', but only in a specific context @h@.
type (p -?># q) h = forall a. Sing a -> p @@ a -> h (Decision (q @@ a))

-- | A proving function for predicate @p@.  See 'Provable' for more
-- information.
type Prove p = forall a. Sing a -> p @@ a

-- | We say that @p@ implies @q@ (@p '-->' q@) if, given @p @@ a@, we can
-- always prove @q \@\@ a@.
type p --> q = forall a. Sing a -> p @@ a -> q @@ a

-- | This is implication '-->#', but only in a specific context @h@.
type (p --># q) h = forall a. Sing a -> p @@ a -> h (q @@ a)

infixr 1 -?>
infixr 1 -?>#
infixr 1 -->
infixr 1 -->#

-- | A typeclass for decidable predicates.
--
-- A predicate is decidable if, given any input @a@, you can either prove
-- or disprove @p \@\@ a@.  A @'Decision' (p \@\@ a)@ is a data type
-- that has a branch @p \@\@ a@ and @'Refuted' (p \@\@ a)@.
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

-- | A typeclass for provable predicates (constructivist tautologies).
--
-- A predicate is provable if, given any input @a@, you can generate
-- a proof of @p \@\@ a@.  Essentially, it means that a predicate is "always
-- true".
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
class Provable p where
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

-- | @'Disprovable' p@ is a constraint that @p@ can be disproven.
type Disprovable p = Provable (Not p)

-- | The deciding/disproving function for @'Disprovable' p@.
--
-- Must be called by applying the 'Predicate' to disprove:
--
-- @
-- 'disprove' \@p
-- @
disprove :: forall p. Disprovable p => Prove (Not p)
disprove = prove @(Not p)

-- | If @T :: k -> 'Type'@ is a type constructor, then @'DecidableTC' T@ is
-- a constraint that @T@ is "decidable", in that you have a canonical
-- function:
--
-- @
-- decideTC :: Sing a -> 'Decision' (T a)
-- @
--
-- Is essentially 'Decidable', except with /type constructors/ @k ->
-- 'Type'@ instead of matchable type-level functions (that are @k ~>
-- 'Type'@).
--
-- Mostly is in this library for compatiblity with "traditional" predicates
-- that are GADT type constructors.
--
-- @since 0.1.1.0
type DecidableTC p = Decidable (TyPred p)

-- | The canonical deciding function for @'DecidableTC' t@.
--
-- @since 0.1.1.0
decideTC :: forall t a. DecidableTC t => Sing a -> Decision (t a)
decideTC = decide @(TyPred t)

-- | If @T :: k -> 'Type'@ is a type constructor, then @'ProvableTC' T@ is
-- a constraint that @T@ is "decidable", in that you have a canonical
-- function:
--
-- @
-- proveTC :: Sing a -> T a
-- @
--
-- Is essentially 'Provable', except with /type constructors/ @k -> 'Type'@
-- instead of matchable type-level functions (that are @k ~> 'Type'@).
--
-- Mostly is in this library for compatiblity with "traditional" predicates
-- that are GADT type constructors.
--
-- @since 0.1.1.0
type ProvableTC  p = Provable  (TyPred p)

-- | The canonical proving function for @'DecidableTC' t@.
--
-- @since 0.1.1.0
proveTC :: forall t a. ProvableTC t => Sing a -> t a
proveTC = prove @(TyPred t)

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

instance Decidable Evident
instance Provable Evident where
    prove = id

instance (Decidable p, SingI f) => Decidable (PMap f p) where
    decide = decide @p . ((sing :: Sing f) @@)

instance (Provable p, SingI f) => Provable (PMap f p) where
    prove = prove @p . ((sing :: Sing f) @@)

-- | Compose two implications.
compImpl
    :: forall p q r. ()
    => p --> q
    -> q --> r
    -> p --> r
compImpl f g s = g s . f s

-- | @'Not' p@ is the predicate that @p@ is not true.
data Not :: Predicate k -> Predicate k
type instance Apply (Not p) a = Refuted (p @@ a)

instance Decidable p => Decidable (Not p) where
    decide (x :: Sing a) = decideNot @p @a (decide @p x)

instance Provable (Not Impossible) where
    prove x v = absurd $ v x

-- | Decide @Not p@ based on decisions of @p@.
decideNot
    :: forall p a. ()
    => Decision (p @@ a)
    -> Decision (Not p @@ a)
decideNot = flipDecision

-- | Flip the contents of a decision.  Turn a proof of @a@ into a disproof
-- of not-@a@.
--
-- Note that this is not reversible in general in Haskell.  See
-- 'Data.Type.Predicate.Logic.doubleNegation' for a situation where it is.
--
-- @since 0.1.1.0
flipDecision
    :: Decision a
    -> Decision (Refuted a)
flipDecision = \case
    Proved    p -> Disproved ($ p)
    Disproved v -> Proved v

-- | Map over the value inside a 'Decision'.
mapDecision
    :: (a -> b)
    -> (b -> a)
    -> Decision a
    -> Decision b
mapDecision f g = \case
    Proved    p -> Proved    $ f p
    Disproved v -> Disproved $ mapRefuted g v

-- | Converts a 'Decision' to a 'Maybe'.  Drop the witness of disproof of
-- @a@, returning 'Just' if 'Proved' (with the proof) and 'Nothing' if
-- 'Disproved'.
--
-- @since 0.1.1.0
forgetDisproof
    :: Decision a
    -> Maybe a
forgetDisproof = \case
    Proved    p -> Just p
    Disproved _ -> Nothing

-- | Drop the witness of proof of @a@, returning 'Nothing' if 'Proved' and
-- 'Just' if 'Disproved' (with the disproof).
--
-- @since 0.1.1.0
forgetProof
    :: Decision a
    -> Maybe (Refuted a)
forgetProof = forgetDisproof . flipDecision

-- | Boolean test if a 'Decision' is 'Proved'.
--
-- @since 0.1.1.0
isProved :: Decision a -> Bool
isProved = isJust . forgetDisproof

-- | Boolean test if a 'Decision' is 'Disproved'.
--
-- @since 0.1.1.0
isDisproved :: Decision a -> Bool
isDisproved = isNothing . forgetDisproof

-- | Helper function for a common pattern of eliminating the disproved
-- branch of 'Decision' to certaintify the proof.
--
-- @since 0.1.2.0
elimDisproof
    :: Decision a
    -> Refuted (Refuted a)
    -> a
elimDisproof = \case
    Proved    p -> const p
    Disproved v -> absurd . ($ v)

-- | Change the target of a 'Refuted' with a contravariant mapping
-- function.
--
-- @since 0.1.2.0
mapRefuted
    :: (a -> b)
    -> Refuted b
    -> Refuted a
mapRefuted = flip (.)
