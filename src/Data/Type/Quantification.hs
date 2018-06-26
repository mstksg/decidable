{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeInType    #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Quantification (
    Any(..), entailAny, entailAnyF
  , All(..), entailAll, entailAllF, decideEntailAll
  ) where

import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Type.Elem.Internal

-- | If there exists an @a@ s.t. @p a@, and if @p@ implies @q@, then there
-- must exist an @a@ s.t. @q a@.
entailAny
    :: forall f p q (as :: f k). ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)        -- ^ implication
    -> Any p as
    -> Any q as
entailAny f (Any i x) = Any i (f i x)

-- | If for all @a@ we have @p a@, and if @p@ implies @q@, then for all @a@
-- we must also have @p a@.
entailAll
    :: forall f p q (as ::  f k). ()
    => (forall a. Elem f as a -> p @@ a -> q @@ a)      -- ^ implication
    -> All p as
    -> All q as
entailAll f a = All $ \i -> f i (runAll a i)

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
    :: forall h f p q as. Functor h
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))      -- ^ implication in context
    -> Any p as
    -> h (Any q as)
entailAnyF f = \case
    Any i x -> Any i <$> f i x

-- | If @p@ implies @q@ under some context @h@, and if we have @p a@ for
-- all @a@, then we must have @q a@ for all @a@ under context @h@.
entailAllF
    :: forall h f p q as. (Universe f, Applicative h, SingI as)
    => (forall a. Elem f as a -> p @@ a -> h (q @@ a))    -- ^ implication in context
    -> All p as
    -> h (All q as)
entailAllF f a = genAllA (\i _ -> f i (runAll a i)) sing

-- | If we have @p a@ for all @a@, and @p a@ can be used to test for @q a@,
-- then we can test all @a@s for @q a@.
decideEntailAll
    :: forall f p q (as ::  f k). (Universe f, SingI as)
    => (forall a. Elem f as a -> p @@ a -> Decision (q @@ a))     -- ^ decidable implication
    -> All p as
    -> Decision (All q as)
decideEntailAll f a = decideAll (\i _ -> f i (runAll a i)) sing

