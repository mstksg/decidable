{-# LANGUAGE AllowAmbiguousTypes    #-}
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
  , TestF, Test
  , Decide(..)
  , type (-?>)
  , type (-->)
  , type Not
  , type (&&&)
  , type (|||)
  , type (^^^)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Not)

type Predicate k = k ~> Type

type TestF f w p = forall a. w a -> f @@ (p @@ a)
type Test w p = TestF (TyCon Decision) w p

type w -?> p = Test w p
type w --> p = TestF IdSym0 w p
infixr 2 -?>
infixr 2 -->

class Decide w p | p -> w where
    decide :: w -?> p

instance (SDecide k, SingI (a :: k)) => Decide Sing (TyCon1 ((:~:) a)) where
    decide = (sing %~)

data Not :: (k ~> Type) -> (k ~> Type)
type instance Apply (Not p) a = Refuted (p @@ a)

instance Decide w p => Decide w (Not p) where
    decide x = case decide @_ @p x of
      Proved p    -> Disproved ($ p)
      Disproved v -> Proved v

data (&&&) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p &&& q) a = (p @@ a, q @@ a)
infixr 3 &&&

instance (Decide w p, Decide w q) => Decide w (p &&& q) where
    decide x = case decide @_ @p x of
      Proved p -> case decide @_ @q x of
        Proved q -> Proved (p, q)
        Disproved v -> Disproved $ \(_, q) -> v q
      Disproved v -> Disproved $ \(p, _) -> v p

data (|||) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)
type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)
infixr 2 |||

instance (Decide w p, Decide w q) => Decide w (p ||| q) where
    decide x = case decide @_ @p x of
      Proved p -> Proved $ Left p
      Disproved v -> case decide @_ @q x of
        Proved q -> Proved $ Right q
        Disproved w -> Disproved $ \case
          Left p  -> v p
          Right q -> w q

type p ^^^ q = (p &&& Not q) ||| (Not p &&& q)
