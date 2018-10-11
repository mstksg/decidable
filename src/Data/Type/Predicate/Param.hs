{-# LANGUAGE ConstraintKinds      #-}
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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Data.Type.Universe.Param
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Manipulate "parameterized predicates".  See 'ParamPred' and 'Found' for
-- more information.
--
module Data.Type.Predicate.Param (
  -- * Parameterized Predicates
    ParamPred
  , FlipPP, ConstPP, PPMap, InP, AnyMatch
  -- * Deciding and Proving
  , Found
  , Searchable, search
  , Selectable, select
  ) where

import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Sigma
import           Data.Type.Predicate
import           Data.Type.Predicate.Logic
import           Data.Type.Universe

-- | A parameterized predicate.  See 'Found' for more information.
type ParamPred k v = k -> Predicate v

-- | Convert a parameterized predicate into a predicate on the parameter.
--
-- A @'Found' p@ is a predicate on @p :: 'ParamPred' k v@ that tests a @k@
-- for the fact that there exists a @v@ where @'ParamPred' k v@ is satisfied.
--
-- Intended as the basic interface for 'ParamPred', since it turns
-- a 'ParamPred' into a normal 'Predicate', which can have 'Decidable' and
-- 'Provable' instances.
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

-- | Promote a @'Predicate' v@ to a @'ParamPred' k v@, ignoring the @k@
-- input.
data ConstPP :: Predicate v -> ParamPred k v
type instance Apply (ConstPP p k) v = p @@ v

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

-- | A constraint that a @'ParamPred' k v@ is "searchable".  It means that
-- for any input @x :: k@, we can prove or disprove that there exists a @y
-- :: v@ that satisfies @P x \@\@ y@.  We can "search" for that @y@, and
-- prove that it can or cannot be found.
type Searchable p = Decidable (Found p)

-- | A constraint that a @'ParamPred' k v@ s "selectable".  It means that
-- for any input @x :: k@, we can always find a @y :: v@ that satisfies @P
-- x \@\@ y@.  We can "select" that @y@, no matter what.
type Selectable p = Provable  (Found p)

-- | The deciding/searching function for @'Searchable' p@.
--
-- Must be called by applying the 'ParamPred':
--
-- @
-- 'search' \@p
-- @
search
    :: forall p. Searchable p
    => Decide (Found p)
search = decide @(Found p)

-- | The proving/selecting function for @'Selectable' p@.
--
-- Must be called by applying the 'ParamPred':
--
-- @
-- 'select' \@p
-- @
select
    :: forall p. Selectable p
    => Prove (Found p)
select = prove @(Found p)

-- | A @'ParamPred' (f k) k@.  Parameterized on an @as :: f k@, returns
-- a predicate that is true if there exists any @a :: k@ in @as@.
--
-- Essentially 'NotNull'.
type InP f = (ElemSym1 f :: ParamPred (f k) k)

instance Universe f => Decidable (Found (InP f)) where
    decide xs = case decide @(NotNull f) xs of
      Proved (WitAny i s) -> Proved $ s :&: i
      Disproved v         -> Disproved $ \case
        s :&: i -> v $ WitAny i s

instance Decidable (NotNull f ==> Found (InP f))
instance Provable (NotNull f ==> Found (InP f)) where
    prove _ (WitAny i s) = s :&: i

instance Decidable (Found (InP f) ==> NotNull f)
instance Provable (Found (InP f) ==> NotNull f) where
    prove _ (s :&: i) = WitAny i s

-- | @'AnyMatch' f@ takes a parmaeterized predicate on @k@ (testing for
-- a @v@) and turns it into a parameterized predicate on @f k@ (testing for
-- a @v@).  It "lifts" the domain into @f@.
--
-- An @'AnyMatch' f p as@ is a predicate taking an argument @a@ and
-- testing if @p a :: 'Predicate' k@ is satisfied for any item in @as ::
-- f k@.
--
-- A @'ParamPred' k v@ tests if a @k@ can create some @v@.  The resulting
-- @'ParamPred' (f k) v@ tests if any @k@ in @f k@ can create some @v@.
data AnyMatch f :: ParamPred k v -> ParamPred (f k) v
type instance Apply (AnyMatch f p as) a = Any f (FlipPP p a) @@ as

instance (Universe f, Decidable (Found p)) => Decidable (Found (AnyMatch f p)) where
    decide xs = case decide @(Any f (Found p)) xs of
      Proved (WitAny i (x :&: p)) -> Proved $ x :&: WitAny i p
      Disproved v                 -> Disproved $ \case
        x :&: WitAny i p -> v $ WitAny i (x :&: p)

