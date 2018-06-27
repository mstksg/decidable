{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Predicate (
    Test
  , type (&&&), decideAnd
  , type (|||), decideOr
  , type (-->)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH

type Test p = forall a. Sing a -> Decision (p @@ a)

data (&&&) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p &&& q) a = (p @@ a, q @@ a)

decideAnd
    :: Test p
    -> Test q
    -> Test (p &&& q)
decideAnd f g x = case f x of
    Proved p -> case g x of
      Proved q -> Proved (p, q)
      Disproved v -> Disproved $ \(_, q) -> v q
    Disproved v -> Disproved $ \(p, _) -> v p

data (|||) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)

decideOr
    :: Test p
    -> Test q
    -> Test (p ||| q)
decideOr f g x = case f x of
    Proved p -> Proved $ Left p
    Disproved v -> case g x of
      Proved q -> Proved $ Right q
      Disproved w -> Disproved $ \case
        Left p  -> v p
        Right q -> w q

data (-->) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p --> q) a = p @@ a -> q @@ a
