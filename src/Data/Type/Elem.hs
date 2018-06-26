{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeInType    #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Elem (
    Elem
  , Index(..)
  , IsJust(..)
  , NEIndex(..)
  , Snd(..)
  ) where

import           Data.Kind
import           Data.List.NonEmpty      (NonEmpty(..))
import           Data.Type.Elem.Internal
import           Prelude hiding          (any, all)


-- | Witness an item in a type-level list by providing its index.
data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

type instance Elem [] = Index

-- | Witness an item in a type-level 'Maybe' by proving the 'Maybe' is
-- 'Just'.
data IsJust :: Maybe k -> k -> Type where
    IsJust :: IsJust ('Just a) a

type instance Elem Maybe = IsJust

-- | Witness an item in a type-level 'NonEmpty' by either indicating that
-- it is the "head", or by providing an index in the "tail".
data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

type instance Elem NonEmpty = NEIndex

-- | Trivially witness an item in the second field of a type-level tuple.
data Snd :: (j, k) -> k -> Type where
    Snd :: Snd '(a, b) b

type instance Elem ((,) j) = Snd
