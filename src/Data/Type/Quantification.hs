{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Quantification (
  -- * Existential Quantification
    Any(..), entailAny, entailAnyF
  , entailAny', entailAnyF'
  -- * Universal Quantification
  , All(..), entailAll, entailAllF, decideEntailAll
  , entailAll', entailAllF', decideEntailAll'
  -- * Subset relationship
  , Subset(..), makeSubset
  , subsetToList, subsetToAny, subsetToAll
  ) where

import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Type.Elem.Internal
import           Data.Type.Universe

-- | A @'Subset' p as@ describes a subset of type-level collection @as@.
newtype Subset p (as :: f k) = Subset { runSubset :: forall a. Elem f as a -> Decision (p @@ a) }

-- | Create a 'Subset' from a predicate.
makeSubset
    :: forall f p (as :: f k). Universe f
    => (forall a. Elem f as a -> Sing a -> Decision (p @@ a))
    -> Sing as
    -> Subset p as
makeSubset f xs = Subset $ \i -> f i (select i xs)

-- | Turn a 'Subset' into a list of satisfied predicates.
subsetToList
    :: forall f p (as :: f k). (Universe f, SingI as)
    => Subset p as
    -> [Any p as]
subsetToList s = foldMapUni go sing
  where
    go :: Elem f as a -> Sing a -> [Any p as]
    go i _ = case runSubset s i of
      Proved p    -> [Any i p]
      Disproved _ -> []

-- | Restrict a 'Subset' to a single (arbitrary) member, or fail if none
-- exists.
subsetToAny
    :: forall f p (as :: f k). (Universe f, SingI as)
    => Subset p as
    -> Decision (Any p as)
subsetToAny s = decideAny (\i _ -> runSubset s i) sing

-- | Test if a subset is equal to the entire original collection
subsetToAll
    :: forall f p (as :: f k). (Universe f, SingI as)
    => Subset p as
    -> Decision (All p as)
subsetToAll s = decideAll (\i _ -> runSubset s i) sing

-- | If there exists an @a@ s.t. @p a@, and if @p@ implies @q@, then there
-- must exist an @a@ s.t. @q a@.
entailAny
    :: forall f p q as. ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)        -- ^ implication
    -> Any p as
    -> Any q as
entailAny f (Any i x) = Any i (f i x)

-- | 'entailAny', but without the membership witness.
entailAny'
    :: forall f p q (as :: f k). ()
    => (forall a. p @@ a -> q @@ a)        -- ^ implication
    -> Any p as
    -> Any q as
entailAny' f = entailAny @f @p @q (\(_ :: Elem f as a) -> f @a)

-- | If for all @a@ we have @p a@, and if @p@ implies @q@, then for all @a@
-- we must also have @p a@.
entailAll
    :: forall f p q as. ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)      -- ^ implication
    -> All p as
    -> All q as
entailAll f a = All $ \i -> f i (runAll a i)

-- | 'entailAll', but without the membership witness.
entailAll'
    :: forall f p q (as :: f k). ()
    => (forall a. p @@ a -> q @@ a)        -- ^ implication
    -> All p as
    -> All q as
entailAll' f = entailAll @f @p @q (\(_ :: Elem f as a) -> f @a)

-- | If @p@ implies @q@ under some context @h@, and if there exists some
-- @a@ such that @p a@, then there must exist some @a@ such that @p q@
-- under that context @h@.
--
-- @h@ might be something like, say, 'Maybe', to give predicate that is
-- either provably true or unprovably false.
--
-- Note that it is not possible to do this with @p a -> 'Decision' (q a)@.
-- This is if the @p a -> 'Decision' (q a)@ implication is false, there
-- it doesn't mean that there is /no/ @a@ such that @q a@, necessarily.
-- There could have been an @a@ where @p@ does not hold, but @q@ does.
entailAnyF
    :: forall f p q as h. Functor h
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))      -- ^ implication in context
    -> Any p as
    -> h (Any q as)
entailAnyF f = \case
    Any i x -> Any i <$> f i x

-- | 'entailAnyF', but without the membership witness.
entailAnyF'
    :: forall f p q (as :: f k) h. Functor h
    => (forall a. p @@ a -> h (q @@ a))      -- ^ implication in context
    -> Any p as
    -> h (Any q as)
entailAnyF' f = entailAnyF @f @p @q (\(_ :: Elem f as a) -> f @a)

-- | If @p@ implies @q@ under some context @h@, and if we have @p a@ for
-- all @a@, then we must have @q a@ for all @a@ under context @h@.
entailAllF
    :: forall f p q as h. (Universe f, Applicative h, SingI as)
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))    -- ^ implication in context
    -> All p as
    -> h (All q as)
entailAllF f a = genAllA (\i _ -> f i (runAll a i)) sing

-- | 'entailAllF', but without the membership witness.
entailAllF'
    :: forall f p q (as :: f k) h. (Universe f, Applicative h, SingI as)
    => (forall a. p @@ a -> h (q @@ a))      -- ^ implication in context
    -> All p as
    -> h (All q as)
entailAllF' f = entailAllF @f @p @q (\(_ :: Elem f as a) -> f @a)

-- | If we have @p a@ for all @a@, and @p a@ can be used to test for @q a@,
-- then we can test all @a@s for @q a@.
decideEntailAll
    :: forall f p q as. (Universe f, SingI as)
    => (forall a. Elem f as a -> p @@ a -> Decision (q @@ a))     -- ^ decidable implication
    -> All p as
    -> Decision (All q as)
decideEntailAll f a = decideAll (\i _ -> f i (runAll a i)) sing

-- | 'decideEntailAll', but without the membeship witness.
decideEntailAll'
    :: forall f p q (as :: f k). (Universe f, SingI as)
    => (forall a. p @@ a -> Decision (q @@ a))     -- ^ decidable implication
    -> All p as
    -> Decision (All q as)
decideEntailAll' f = decideEntailAll @f @p @q (\(_ :: Elem f as a) -> f @a)

