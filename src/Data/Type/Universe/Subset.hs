{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.Universe.Subset
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Represent a decidable subset of a type-level collection.
--
module Data.Type.Universe.Subset (
  -- * Subset
    Subset, WitSubset(..)
  , makeSubset
  -- ** Subset manipulation
  , intersection, union, symDiff, mergeSubset, imergeSubset
  , mapSubset, imapSubset
  -- ** Subset extraction
  , subsetToList
  -- ** Subset tests
  , subsetToAny, subsetToAll, subsetToNone
  -- ** Subset construction
  , emptySubset, fullSubset
  ) where

import           Control.Applicative
import           Data.Kind
import           Data.Monoid                        (Alt(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Type.Functor.Product
import           Data.Type.Predicate
import           Data.Type.Predicate.Logic
import           Data.Type.Predicate.Quantification
import           Data.Type.Universe

-- | A @'WitSubset' f p @@ as@ describes a /decidable/ subset of type-level
-- collection @as@.
newtype WitSubset f p (as :: f k) = WitSubset
    { runWitSubset :: forall a. Elem f as a -> Decision (p @@ a)
    }

-- | A @'Subset' f p@ is a predicate that some decidable subset of an input
-- @as@ is true.
data Subset f :: (k ~> Type) -> (f k ~> Type)
type instance Apply (Subset f p) as = WitSubset f p as

instance (Universe f, Decidable p) => Decidable (Subset f p)
instance (Universe f, Decidable p) => Provable (Subset f p) where
    prove = makeSubset @f @_ @p (\_ -> decide @p)

-- | Create a 'Subset' from a predicate.
makeSubset
    :: forall f k p (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
    -> Sing as
    -> Subset f p @@ as
makeSubset f xs = WitSubset $ \i -> f i (indexSing i xs)

-- | Turn a 'Subset' into a list (or any 'Alternative') of satisfied
-- predicates.
--
-- List is meant to include no duplicates.
subsetToList
    :: forall f p t. (Universe f, Alternative t)
    => (Subset f p --># Any f p) t
subsetToList xs s = getAlt $ (`ifoldMapSing` xs) $ \i _ -> Alt $ case runWitSubset s i of
    Proved p    -> pure $ WitAny i p
    Disproved _ -> empty

-- | Restrict a 'Subset' to a single (arbitrary) member, or fail if none
-- exists.
subsetToAny
    :: forall f p. Universe f
    => Subset f p -?> Any f p
subsetToAny xs s = idecideAny (\i _ -> runWitSubset s i) xs

-- | Construct an empty subset.
emptySubset :: forall f as. (Universe f, SingI as) => Subset f Impossible @@ as
emptySubset = prove @(Subset f Impossible) sing

-- | Construct a full subset
fullSubset :: forall f as. (Universe f, SingI as) => Subset f Evident @@ as
fullSubset = prove @(Subset f Evident) sing

-- | Test if a subset is empty.
subsetToNone :: forall f p. Universe f => Subset f p -?> None f p
subsetToNone xs s = idecideNone (\i _ -> runWitSubset s i) xs

-- | Combine two subsets based on a decision function
imergeSubset
    :: forall f k p q r (as :: f k). ()
    => (forall a. Elem f as a -> Decision (p @@ a) -> Decision (q @@ a) -> Decision (r @@ a))
    -> Subset f p @@ as
    -> Subset f q @@ as
    -> Subset f r @@ as
imergeSubset f ps qs = WitSubset $ \i ->
    f i (runWitSubset ps i) (runWitSubset qs i)

-- | Combine two subsets based on a decision function
mergeSubset
    :: forall f k p q r (as :: f k). ()
    => (forall a. Decision (p @@ a) -> Decision (q @@ a) -> Decision (r @@ a))
    -> Subset f p @@ as
    -> Subset f q @@ as
    -> Subset f r @@ as
mergeSubset f = imergeSubset (\(_ :: Elem f as a) p -> f @a p)

-- | Subset intersection
intersection
    :: forall f p q. ()
    => ((Subset f p &&& Subset f q) --> Subset f (p &&& q))
intersection _ = uncurry $ imergeSubset $ \(_ :: Elem f as a) -> decideAnd @p @q @a

-- | Subset union (left-biased)
union
    :: forall f p q. ()
    => ((Subset f p &&& Subset f q) --> Subset f (p ||| q))
union _ = uncurry $ imergeSubset $ \(_ :: Elem f as a) -> decideOr @p @q @a

-- | Symmetric subset difference
symDiff
    :: forall f p q. ()
    => ((Subset f p &&& Subset f q) --> Subset f (p ^^^ q))
symDiff _ = uncurry $ imergeSubset $ \(_ :: Elem f as a) -> decideXor @p @q @a

-- | Test if a subset is equal to the entire original collection
subsetToAll
    :: forall f p. Universe f
    => Subset f p -?> All f p
subsetToAll xs s = idecideAll (\i _ -> runWitSubset s i) xs

-- | 'mapSubset', but providing an 'Elem'.
imapSubset
    :: (forall a. Elem f as a -> p @@ a -> q @@ a)
    -> (forall a. Elem f as a -> q @@ a -> p @@ a)
    -> Subset f p @@ as
    -> Subset f q @@ as
imapSubset f g s = WitSubset $ \i ->
    mapDecision (f i) (g i) (runWitSubset s i)

-- | Map a bidirectional implication over a subset described by that
-- implication.
--
-- Implication needs to be bidirectional, or otherwise we can't produce
-- a /decidable/ subset as a result.
mapSubset
    :: Universe f
    => (p --> q)
    -> (q --> p)
    -> (Subset f p --> Subset f q)
mapSubset f g xs = withSingI xs $
    imapSubset (\i -> f (indexSing i xs))
               (\i -> g (indexSing i xs))
