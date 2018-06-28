{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
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
    Predicate
  , Pred(..)
  , TestF, Test
  , Decide(..), Imply(..)
  , type (-?>)
  , type (-->)
  , type Not, proveNot
  , type (&&&), proveAnd
  , type (|||), proveOr
  , type (^^^), proveXor
  , (:=>)(..), type (==>)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Not)

type Predicate k = k ~> Type

type TestF f w p = forall a. w @@ a -> f @@ (p @@ a)
type Test w p = TestF (TyCon1 Decision) w p

type w --> p = TestF IdSym0 w p
infixr 2 -->
type w -?> p = Test w p
infixr 2 -?>

class Decide w p | p -> w where
    decide :: TyCon1 w -?> p

-- | maybe can be changed to fmap?
class Imply w p | p -> w where
    imply :: w --> p

newtype Pred p a = Pred { getPred :: p @@ a }

-- instance Decide (Pred (TyCon1 Decision .@#@$$$ p)) p where
--     decide (Pred x) = x

instance (SDecide k, SingI (a :: k)) => Decide Sing (TyCon1 ((:~:) a)) where
    decide = (sing %~)

data Not :: (k ~> Type) -> (k ~> Type)
type instance Apply (Not p) a = Refuted (p @@ a)

instance Decide w p => Decide w (Not p) where
    decide (x :: w a) = proveNot @p @a (decide @_ @p x)

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

instance (Decide w p, Decide w q) => Decide w (p &&& q) where
    decide (x :: w a) = proveAnd @p @q @a (decide @_ @p x) (decide @_ @q x)

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

instance (Decide w p, Decide w q) => Decide w (p ||| q) where
    decide (x :: w a) = proveOr @p @q @a (decide @_ @p x) (decide @_ @q x)

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

data (==>) :: (k -> Constraint) -> (k ~> Type) -> (k ~> Type)

data (:=>) :: (k -> Constraint) -> (k ~> Type) -> k -> Type where
    Wit :: c a => p @@ a -> (c :=> p) a

type instance Apply (c ==> p) a = (c :=> p) a
