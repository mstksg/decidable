{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE EmptyCase              #-}
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
-- TODO: explain matchable function, how to define predicates
--
module Data.Type.Predicate (
    -- * Predicates
    Predicate, Wit(..)
    -- ** Construct Predicates
  , TyPred, Evident, EqualTo, BoolPred, Impossible
    -- ** Manipulate predicates
  , PMap
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

-- | The always-false predicate
data Impossible :: Predicate k
type instance Apply Impossible a = Void

-- | @'EqualTo' a@ is a predicate that the input is equal to @a@.
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

-- | A typeclass for provable predicates (constructivist tautologies).
--
-- A predicate is provable if, given any input @a@, you can generate
-- a proof of @p @@ a@.  Essentially, it means that a predicate is "always
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

instance (Decidable f, SingI g) => Decidable (f .@#@$$$ g) where
    decide = decide @f . ((sing :: Sing g) @@)

instance (Provable f, SingI g) => Provable (f .@#@$$$ g) where
    prove = prove @f . ((sing :: Sing g) @@)

instance Decidable Impossible where
    decide _ = Disproved $ \case {}

-- | Compose two implications.
compImpl
    :: forall p q r. ()
    => p --> q
    -> q --> r
    -> p --> r
compImpl f g s = g s . f s

