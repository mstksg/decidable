{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Predicate.Param (
    ParamPred
  , Found, FlipPP, PPMap
  , search, select
  , AnyMatch
  ) where

import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Sigma
import           Data.Type.Predicate
import           Data.Type.Universe

-- | A parameterized predicate.
type ParamPred k v = k -> Predicate v

-- | Convert a parameterized predicate into a predicate on the parameter
--
-- A @'Found' p@ is a predicate on @p :: 'ParamPred' k v@ that tests a @k@
-- for the fact that there exists a @v@ where @'ParamPred' k v@ is satisfied.
--
-- Meant to be used to allow one to write 'Provable' and 'Decidable'
-- instances for @'Found' p@, for a given 'ParamPred' @p@.
--
-- For some context, an instance of @'Provable' ('Found' P)@, where @P ::
-- 'ParamPred' k v@, means that for any input @x :: k@, we can always find
-- a @y :: v@ such that we have @P x @@ y@.
--
-- In the language of quantifiers, it means that forall @x :: k@, there
-- exists a @y :: v@ such that @P x @@ y@.
--
-- For an instance of @'Decidable' ('Found' P)@, it means that for all @x
-- :: k@, we can prove or disprove the fact that there exists a @y :: v@
-- such that @P x @@ y@.
data Found :: ParamPred k v -> Predicate k
type instance Apply (Found (p :: ParamPred k v)) a = Σ v (p a)

-- | Flip the arguments of a 'ParamPred'.
data FlipPP :: ParamPred v k -> ParamPred k v
type instance Apply (FlipPP p x) y = p y @@ x

-- | Pre-compose a function to a 'ParamPred'.  Is essentially @'flip'
-- ('.')@, but unfortunately defunctionalization doesn't work too well with
-- that definition.
data PPMap :: (k ~> j) -> ParamPred j v -> ParamPred k v
type instance Apply (PPMap f p x) y = p (f @@ x) @@ y

instance (Decidable (Found (p :: ParamPred j v)), SingI (f :: k ~> j)) => Decidable (Found (PPMap f p)) where
    decide (x :: Sing a) = case decide @(Found p) ((sing :: Sing f) @@ x) of
        Proved (i :&: p) -> Proved $ i :&: p
        Disproved v      -> Disproved $ \case i :&: p -> v (i :&: p)

instance (Provable (Found (p :: ParamPred j v)), SingI (f :: k ~> j)) => Provable (Found (PPMap f p)) where
    prove (x :: Sing a) = case prove @(Found p) ((sing :: Sing f) @@ x) of
        i :&: p -> i :&: p

-- | Convenient alias for 'decide' in the case of @'Found' p@; basically
-- like 'decide' for a 'ParamPred'.  Saying that predicate @'Found' p@ is
-- decidable means that, for an input @x :: k@, we can prove or disprove
-- that there exists a @y :: v@ that satisfies @P x @@ y@.
--
-- Can be called by applying the 'ParamPred':
--
-- @
-- 'search' \@p
-- @
search
    :: forall p. Decidable (Found p)
    => Decide (Found p)
search = decide @(Found p)

-- | Convenient alias for 'prove' in the case of @'Found' p@; basically
-- like 'prove' for 'ParamPred'.  You can imagine it as generating the
-- witness for "forall @x :: k@. exists @y :: v@. P x @@ y".
--
-- Can be called by applying the 'ParamPred':
--
-- @
-- 'select' \@p
-- @
select
    :: forall p. Provable (Found p)
    => Prove (Found p)
select = prove @(Found p)

-- | @'AnyMatch' f@ takes a parmaeterized predicate on @k@ (testing for
-- a @v@) and turns it into a parameterized predicate on @f k@ (testing for
-- a @v@).  It "lifts" the domain into @f@.
--
-- An @'AnyMatch' f p as@ is a predicate taking an argument @a@ and
-- testing if @p a :: 'Predicate' k@ is satisfied for any item in @as ::
-- f k@.
--
-- A @'ParamPred' k v@ tests if a @k@ can create some @v@.  The resulting
-- @'Param' (f k) v@ tests if any @k@ in @f k@ can create some @v@.
data AnyMatch f :: ParamPred k v -> ParamPred (f k) v
type instance Apply (AnyMatch f p as) a = Any f (FlipPP p a) @@ as

instance (Universe f, Decidable (Found p)) => Decidable (Found (AnyMatch f p)) where
    decide xs = case decide @(Any f (Found p)) xs of
      Proved (WitAny i (x :&: p)) -> Proved $ x :&: WitAny i p
      Disproved v                 -> Disproved $ \case
        x :&: WitAny i p -> v $ WitAny i (x :&: p)

