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
  , type Not, proveNot
  , type (&&&), proveAnd
  , type (|||), proveOr
  , type (^^^), proveXor
    -- * Decidable Predicates
  , Test, type (-?>), type (-?>#)
  , Test_, type (-->), type (-->#)
  , Decide(..), Decide_(..)
  , DFunctor(..), TFunctor(..)
  , compImpl
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Not)

type Predicate k = k ~> Type

-- | Convert a normal '->' type constructor into a 'Predicate'.
--
-- @
-- 'TyPred' :: (k -> 'Type') -> 'Predicate' k
-- @
type TyPred = (TyCon1 :: (k -> Type) -> Predicate k)

-- | The always-true predicate.
type Evident = (TyPred Sing :: Predicate k)

type EqualTo a = TyCon1 ((:~:) a)

-- | Convert a propositional predicate into a 'Predicate'
--
-- @
-- 'BoolPred' :: (k ~> Bool) -> Predicate k
-- @
type BoolPred (p :: k ~> Bool) = (EqualTo 'True .@#@$$$ p :: Predicate k)

type PMap (f :: k ~> j) (p :: Predicate j) = (p .@#@$$$ f :: Predicate k)

newtype Wit p a = Wit { getWit :: p @@ a }

type Test  p = forall a. Sing a -> Decision (p @@ a)
type p -?> q = forall a. Sing a -> p @@ a -> Decision (q @@ a)
type (p -?># q) h = forall a. Sing a -> p @@ a -> h (Decision (q @@ a))

type Test_ p = forall a. Sing a -> p @@ a
type p --> q = forall a. Sing a -> p @@ a -> q @@ a
type (p --># q) h = forall a. Sing a -> p @@ a -> h (q @@ a)

infixr 2 -?>
infixr 2 -?>#
infixr 2 -->
infixr 2 -->#

class Decide p where
    decide :: Test p

    default decide :: Decide_ p => Test p
    decide = Proved . decide_ @p

class Decide p => Decide_ p where
    decide_ :: Test_ p

class DFunctor f where
    dmap :: forall p q. (p -?> q) -> (f p -?> f q)

class TFunctor f where
    tmap :: forall p q. (p --> q) -> (f p --> f q)

instance (SDecide k, SingI (a :: k)) => Decide (EqualTo a) where
    decide = (sing %~)

instance Decide  Evident
instance Decide_ Evident where
    decide_ = id

instance (Decide f, SingI g) => Decide (f .@#@$$$ g) where
    decide = decide @f . ((sing :: Sing g) @@) 

instance (Decide_ f, SingI g) => Decide_ (f .@#@$$$ g) where
    decide_ = decide_ @f . ((sing :: Sing g) @@) 

data Not :: (k ~> Type) -> (k ~> Type)
type instance Apply (Not p) a = Refuted (p @@ a)

instance Decide p => Decide (Not p) where
    decide (x :: Sing a) = proveNot @p @a (decide @p x)

proveNot
    :: forall p a. ()
    => Decision (p @@ a)
    -> Decision (Not p @@ a)
proveNot = \case
    Proved p    -> Disproved ($ p)
    Disproved v -> Proved v

data (&&&) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p &&& q) a = (p @@ a, q @@ a)
infixr 3 &&&

instance (Decide p, Decide q) => Decide (p &&& q) where
    decide (x :: Sing a) = proveAnd @p @q @a (decide @p x) (decide @q x)

proveAnd
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p &&& q) @@ a)
proveAnd = \case
    Proved p    -> \case
      Proved q    -> Proved (p, q)
      Disproved v -> Disproved $ \(_, q) -> v q
    Disproved v -> \_ -> Disproved $ \(p, _) -> v p

data (|||) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)
infixr 2 |||

instance (Decide p, Decide q) => Decide (p ||| q) where
    decide (x :: Sing a) = proveOr @p @q @a (decide @p x) (decide @q x)

proveOr
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p ||| q) @@ a)
proveOr = \case
    Proved p    -> \_ -> Proved $ Left p
    Disproved v -> \case
      Proved q    -> Proved $ Right q
      Disproved w -> Disproved $ \case
        Left p  -> v p
        Right q -> w q

type p ^^^ q = (p &&& Not q) ||| (Not p &&& q)

proveXor
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p ^^^ q) @@ a)
proveXor p q = proveOr @(p &&& Not q) @(Not p &&& q) @a
                  (proveAnd @p @(Not q) @a p (proveNot @q @a q))
                  (proveAnd @(Not p) @q @a (proveNot @p @a p) q)

compImpl
    :: forall p q r. ()
    => p --> q
    -> q --> r
    -> p --> r
compImpl f g s = g s . f s

