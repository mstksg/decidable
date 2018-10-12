{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- |
-- Module      : Data.Type.Predicate.Auto
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Useful utilities for situations where you know that a predicate @P@ is
-- satisfied for a specific @a@ at compile-time.
--
-- @since 0.1.1.0
module Data.Type.Predicate.Auto (
    Auto(..)
  , AutoElem(..)
  , AutoProvable
  ) where

import           Data.List.NonEmpty        (NonEmpty(..))
import           Data.Singletons
import           Data.Type.Equality
import           Data.Type.Predicate
import           Data.Type.Predicate.Logic
import           Data.Type.Universe

-- | Automatically generate a witness for predicate @p@ applied to input
-- @a@.
--
-- Mostly useful for situations where you know @a@ at compile-time, so you
-- can just write 'auto' directly in your source code.  The choice is
-- intended to mirror the @auto@ keyword in languages like Idris.
--
-- Very close in nature to the @Known@ typeclass in the /type-combinators/
-- library.
class Auto (p :: Predicate k) (a :: k) where
    -- | Have the compiler generate a witness for @p \@\@ a@.
    --
    -- Must be called using type application syntax:
    --
    -- @
    -- 'auto' @_ @p @a
    -- @
    auto :: p @@ a

instance SingI a => Auto Evident a where
    auto = sing

instance Auto (EqualTo a) a where
    auto = Refl

instance (Auto p a, Auto q a) => Auto (p &&& q) a where
    auto = (auto @_ @p @a, auto @_ @q @a)

instance Auto q a => Auto (p ==> q) a where
    auto _ = auto @_ @q @a

-- | Helper "predicate transformer" that gives you an instant 'auto' for
-- any 'Provable' instance.
--
-- For example, say you have predicate @P@ that you know is 'Provable', and
-- you wish to generate a @P \@\@ x@, for some specific @x@ you know at
-- compile-time.  You can use:
--
-- @
-- 'auto' @_ @(AutoProvable P) @x
-- @
--
-- to obtain a @P \@\@ x@.
--
-- 'AutoProvable' is essentially the identity function.
data AutoProvable :: Predicate k -> Predicate k
type instance Apply (AutoProvable p) a = p @@ a

instance (Provable p, SingI a) => Auto (AutoProvable p) a where
    auto = prove @p @a sing

-- | Typeclass representing 'Elem's pointing to an @a :: k@ that can be
-- generated automatically from type-level collection @as :: f k@.  
--
-- If GHC knows both the type-level collection and the element you want to
-- find at compile-time, this instance should allow it to find it.
--
-- Used to help in the instance of 'Auto' for the 'In' predicate.
--
-- Example usage:
--
-- @
-- autoElem :: Index '[1,6,2,3] 2
-- -- IS (IS IZ)        -- third spot
-- @
--
-- And when used with 'Auto':
--
-- @
-- auto @_ @(In [] '[1,6,2,3]) @2
-- -- IS (IS IZ)
-- @
class AutoElem f (as :: f k) (a :: k) where
    -- | Generate the 'Elem' pointing to the @a :: @ in a type-level
    -- collection @as :: f k@.
    autoElem :: Elem f as a

instance {-# OVERLAPPING #-} AutoElem [] (a ': as) a where
    autoElem = IZ

instance {-# OVERLAPPING #-} AutoElem [] as a => AutoElem [] (b ': as) a where
    autoElem = IS autoElem

instance AutoElem Maybe ('Just a) a where
    autoElem = IsJust

instance AutoElem (Either j) ('Right a) a where
    autoElem = IsRight

instance AutoElem NonEmpty (a ':| as) a where
    autoElem = NEHead

instance AutoElem [] as a => AutoElem NonEmpty (b ':| as) a where
    autoElem = NETail autoElem

instance AutoElem f as a => Auto (In f as) a where
    auto = autoElem @f @as @a

