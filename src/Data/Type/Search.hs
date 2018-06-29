{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Type.Search (
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Any)
import           Data.Singletons.Sigma
import           Data.Type.Predicate
import           Data.Type.Universe

data Found v :: (k -> Predicate v) -> Predicate k
type instance Apply (Found v p) a = Σ v (p a)

class Search v (p :: k -> (v ~> Type)) where
    search :: Test (Found v p)

class Search v p => Locate v (p :: k -> (v ~> Type)) where
    locate :: Given (Found v p)

instance Search v p => Decide (Found v p) where
    decide = search

instance Locate v p => Taken (Found v p) where
    taken = locate

-- instance Search v p => Search v (Any f _)
