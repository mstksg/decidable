{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE EmptyCase            #-}
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
  , Searchable(..), Selectable(..)
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
-- See 'Searchable' and 'Selectable' for more information.
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

-- | A parameterized predicate @P :: 'ParamPred' k v@ is searchable if,
-- given an input @x :: k@, we can prove or disprove that you can construct
-- a value @P x @@ y@ for some @y :: v@.
--
-- Essentially, you can "search" for a @v@ that fits.
class Searchable p where
    search :: Decide (Found p)

    default search :: Selectable p => Decide (Found p)
    search = Proved . select

-- | A parameterized predicate @P :: 'ParamPred' k v@ is selectable if,
-- given an input @x :: k@, we can always prove a @P x @@ y@ for some @y ::
-- k@.
--
-- In the language of quantifiers, it means that forall @x :: k@, there
-- exists a @y :: v@ such that @P x @@ y@.
class Searchable p => Selectable p where
    select :: Prove (Found p)

instance Searchable p => Decidable (Found p) where
    decide = search

instance Selectable p => Provable (Found p) where
    prove = select

instance (Searchable (p :: ParamPred j v), SingI (f :: k ~> j)) => Searchable (PPMap f p) where
    search (x :: Sing a) = case search @p ((sing :: Sing f) @@ x) of
        Proved (i :&: p) -> Proved $ i :&: p
        Disproved v      -> Disproved $ \case i :&: p -> v (i :&: p)

instance (Selectable (p :: ParamPred j v), SingI (f :: k ~> j)) => Selectable (PPMap f p) where
    select (x :: Sing a) = case select @p ((sing :: Sing f) @@ x) of
        i :&: p -> i :&: p

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

instance (Universe f, Searchable p) => Searchable (AnyMatch f p) where
    search xs = case decide @(Any f (Found p)) xs of
      Proved (WitAny i (x :&: p)) -> Proved $ x :&: WitAny i p
      Disproved v                 -> Disproved $ \case
        x :&: WitAny i p -> v $ WitAny i (x :&: p)

