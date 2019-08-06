{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

-- |
-- Module      : Data.Type.Universe
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- A type family for "containers", intended for allowing lifting of
-- predicates on @k@ to be predicates on containers @f k@.
--
module Data.Type.Universe (
  -- * Universe
    Elem, In, Universe(..), singAll
  -- ** Instances
  , Index(..), IJust(..), IRight(..), NEIndex(..), ISnd(..), IProxy, IIdentity(..)
  , CompElem(..), SumElem(..)
  , sameIndexVal, sameNEIndexVal
  -- ** Predicates
  , All, WitAll(..), NotAll
  , Any, WitAny(..), None
  , Null, NotNull
  -- *** Specialized
  , IsJust, IsNothing, IsRight, IsLeft
  -- * Decisions and manipulations
  , decideAny, decideAll
  , genAll, igenAll
  , foldMapUni, ifoldMapUni, index, pickElem
  -- * Universe Combination
  -- ** Universe Composition
  , (:.:)(..), sGetComp, GetComp
  , allComp, compAll, anyComp, compAny
  -- ** Universe Disjunction
  , (:+:)(..)
  , anySumL, anySumR, sumLAny, sumRAny
  , allSumL, allSumR, sumLAll, sumRAll
  -- * Defunctionalization symbols
  , ElemSym0, ElemSym1, ElemSym2
  , ProdSym0, ProdSym1, ProdSym2
  , GetCompSym0, GetCompSym1
  -- * Singletons
  , SIndex(..), SIJust(..), SIRight(..), SNEIndex(..), SISnd(..), SIProxy, SIIdentity(..)
  , Sing (SComp, SInL, SIndex', SIJust', SIRight', SNEIndex', SISnd', SIProxy', SIIdentity')
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Predicate
import           Data.Type.Universe.Internal
import           Data.Type.Universe.Prod
import           GHC.Generics                ((:*:)(..))
import           Prelude hiding              (any, all)

-- | 'genAll', but providing an 'Elem'.
igenAll
    :: forall f k (p :: k ~> Type) (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> p @@ a)            -- ^ always-true predicate on value
    -> (Sing as -> All f p @@ as)                                  -- ^ always-true predicate on collection
igenAll f = prodAll (\(i :*: x) -> f i x) . imapProd (:*:) . singProd

-- | If @p a@ is true for all values @a@ in @as@, then we have @'All'
-- p as@.  Basically witnesses the definition of 'All'.
genAll
    :: forall f k (p :: k ~> Type). Universe f
    => Prove p                 -- ^ always-true predicate on value
    -> Prove (All f p)         -- ^ always-true predicate on collection
genAll f = prodAll f . singProd

-- | Split a @'Sing' as@ into a proof that all @a@ in @as@ exist.
singAll
    :: forall f k (as :: f k). Universe f
    => Sing as
    -> All f Evident @@ as
singAll = prodAll id . singProd

-- | Test that a 'Maybe' is 'Just'.
--
-- @since 0.1.2.0
type IsJust    = (NotNull Maybe :: Predicate (Maybe k))

-- | Test that a 'Maybe' is 'Nothing'.
--
-- @since 0.1.2.0
type IsNothing = (Null    Maybe :: Predicate (Maybe k))

-- | Test that an 'Either' is 'Right'
--
-- @since 0.1.2.0
type IsRight = (NotNull (Either j) :: Predicate (Either j k))

-- | Test that an 'Either' is 'Left'
--
-- @since 0.1.2.0
type IsLeft  = (Null    (Either j) :: Predicate (Either j k))
