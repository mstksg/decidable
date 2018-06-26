{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeInType    #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Elem.Internal (
    Elem, Universe(..)
  , Any(..), All(..)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Prelude hiding         (any, all)

-- | A witness for membership of a given item in a type-level collection
type family Elem (f :: Type -> Type) :: f k -> k -> Type

-- | An @'Any' p as@ is a witness that, for at least one item @a@ in the
-- type-level collection @as@, the predicate @p a@ is true.
data Any :: (k ~> Type) -> f k -> Type where
    Any :: Elem f as a -> p @@ a -> Any p as

-- | An @'All' p as@ is a witness that, the predicate @p a@ is true for all
-- items @a@ in the type-level collection @as@.
newtype All p (as :: f k) = All { runAll :: forall a. Elem f as a -> p @@ a }

-- | Typeclass for a type-level container that you can quantify or lift
-- type-level predicates over.
class Universe (f :: Type -> Type) where

    -- | You should read this type as:
    --
    -- @
    -- 'decideAny'' :: ('Sing' a  -> 'Decision' (p a)    )
    --            -> (Sing as -> Decision (Any p as)
    -- @
    --
    -- It lifts a predicate @p@ on an individual @a@ into a predicate that
    -- on a collection @as@ that is true if and only if /any/ item in @as@
    -- satisfies the original predicate.
    --
    -- That is, it turns a predicate of kind @k ~> Type@ into a predicate
    -- of kind @f k ~> Type@.
    --
    -- Essentially tests existential quantification.
    decideAny
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
        -> (Sing as -> Decision (Any p as))                         -- ^ predicate on collection

    -- | You should read this type as:
    --
    -- @
    -- 'decideAll'' :: ('Sing' a  -> 'Decision' (p a)    )
    --            -> ('Sing' as -> 'Decision' (All p as)
    -- @
    --
    -- It lifts a predicate @p@ on an individual @a@ into a predicate that
    -- on a collection @as@ that is true if and only if /all/ items in @as@
    -- satisfies the original predicate.
    --
    -- That is, it turns a predicate of kind @k ~> Type@ into a predicate
    -- of kind @f k ~> Type@.
    --
    -- Essentially tests universal quantification.
    decideAll
        :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))   -- ^ predicate on value
        -> (Sing as -> Decision (All p as))                         -- ^ predicate on collection

    -- | If @p a@ is true for all values @a@ in @as@ under some
    -- (Applicative) context @h@, then you can create an @'All' p as@ under
    -- that Applicative context @h@.
    --
    -- Can be useful with 'Identity' (which is basically unwrapping and
    -- wrapping 'All'), or with 'Maybe' (which can express predicates that
    -- are either provably true or not provably false).
    genAllA
        :: forall k (p :: k ~> Type) (as :: f k) h. Applicative h
        => (forall a. Elem f as a -> Sing a -> h (p @@ a))        -- ^ predicate on value in context
        -> (Sing as -> h (All p as))                              -- ^ predicate on collection in context

