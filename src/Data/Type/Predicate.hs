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
    type (-?>)
  , type (&&&), decideAnd
  , type (|||), decideOr
  , type (-->)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH

-- type Test p = forall a. Sing a -> Decision (p @@ a)

type f -?> p = forall a. f a -> Decision (p @@ a)

data (&&&) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p &&& q) a = (p @@ a, q @@ a)

decideAnd
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p &&& q) @@ a)
decideAnd = \case
    Proved p -> \case
      Proved q -> Proved (p, q)
      Disproved v -> Disproved $ \(_, q) -> v q
    Disproved v -> \_ -> Disproved $ \(p, _) -> v p

data (|||) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p ||| q) a = Either (p @@ a) (q @@ a)

decideOr
    :: forall p q a. ()
    => Decision (p @@ a)
    -> Decision (q @@ a)
    -> Decision ((p ||| q) @@ a)
decideOr = \case
    Proved p -> \_ -> Proved $ Left p
    Disproved v -> \case
      Proved q -> Proved $ Right q
      Disproved w -> Disproved $ \case
        Left p  -> v p
        Right q -> w q

data (-->) :: (k ~> Type) -> (k ~> Type) -> (k ~> Type)

type instance Apply (p --> q) a = p @@ a -> q @@ a
