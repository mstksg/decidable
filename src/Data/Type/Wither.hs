{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Wither (
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Sigma
import           Data.Type.Universe
import           Data.Type.Quantification

class Universe f => Wither f where
    wither :: forall k p (as :: f k). ()
           => (forall a. Elem f as a -> Sing a -> p @@ a)
           -> Sing as
           -> SomeSing k
