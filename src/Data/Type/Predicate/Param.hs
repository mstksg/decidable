{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
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
  , IsTC, EqBy
  , FlipPP, ConstPP, PPMap, PPMapV, InP, AnyMatch, TyPP
  -- * Deciding and Proving
  , Found, NotFound
  , Selectable, select
  , Searchable, search
  , inPNotNull, notNullInP
  -- ** Type Constructors
  , SelectableTC, selectTC
  , SearchableTC, searchTC
  -- * Combining
  , OrP, AndP
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude.Tuple
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
-- a @y :: v@ such that we have @P x \@\@ y@.
--
-- In the language of quantifiers, it means that forall @x :: k@, there
-- exists a @y :: v@ such that @P x \@\@ y@.
--
-- For an instance of @'Decidable' ('Found' P)@, it means that for all @x
-- :: k@, we can prove or disprove the fact that there exists a @y :: v@
-- such that @P x \@\@ y@.
data Found :: ParamPred k v -> Predicate k
type instance Apply (Found (p :: ParamPred k v)) a = Σ v (p a)

-- | Convert a parameterized predicate into a predicate on the parameter.
--
-- A @'Found' p@ is a predicate on @p :: 'ParamPred' k v@ that tests a @k@
-- for the fact that there /cannot exist/ a @v@ where @'ParamPred' k v@ is
-- satisfied.  That is, @'NotFound' P \@\@ x@ is satisfied if no @y :: v@
-- can exist where @P x \@\@ y@ is satisfied.
--
-- For some context, an instance of @'Provable' ('NotFound' P)@, where @P
-- :: 'ParamPred' k v@, means that for any input @x :: k@, we can always
-- reject any @y :: v@ that claims to satisfy @P x \@\@ y@.
--
-- In the language of quantifiers, it means that forall @x :: k@, there
-- does not exist a @y :: v@ such that @P x \@\@ y@.
--
-- For an instance of @'Decidable' ('Found' P)@, it means that for all @x
-- :: k@, we can prove or disprove the fact that there does not exist a @y
-- :: v@ such that @P x \@\@ y@.
--
-- @since 0.1.2.0
type NotFound (p :: ParamPred k v) = (Not (Found p) :: Predicate k)

-- | Flip the arguments of a 'ParamPred'.
data FlipPP :: ParamPred v k -> ParamPred k v
type instance Apply (FlipPP p x) y = p y @@ x

-- | Promote a @'Predicate' v@ to a @'ParamPred' k v@, ignoring the @k@
-- input.
data ConstPP :: Predicate v -> ParamPred k v
type instance Apply (ConstPP p k) v = p @@ v

-- | @Found ('EqBy' f) \@\@ x@ is true if there exists some value when,
-- with @f@ applied to it, is equal to @x@.
--
-- See 'IsTC' for a useful specific application.
--
-- @
-- 'EqBy' :: (v ~> k) -> 'ParamPred' k v
-- 'Found' ('EqBy' f) :: 'Predicate' k
-- @
--
-- @since 0.1.5.0
data EqBy :: (v ~> k) -> ParamPred k v
type instance Apply (EqBy f x) y = x :~: (f @@ y)

-- | @Found ('IsTC' t) \@\@ x@ is true if @x@ was made using the unary type
-- constructor @t@.
--
-- For example:
--
-- @
-- type IsJust = (Found (IsTC 'Just) :: Predicate (Maybe v))
-- @
--
-- makes a predicate where @IsJust \@\@ x@ is true if @x@ is 'Just', and
-- false if @x@ is 'Nothing'.
--
-- For a more general version, see 'EqBy'
--
-- The kind of 'IsTC' is:
--
-- @
-- 'IsTC' :: (v -> k) -> 'ParamPred' k v
-- 'Found' ('IsTC' t) :: 'Predicate' k
-- @
--
-- Applied to specific things:
-- 
-- @
-- 'IsTC' ''Just' :: 'ParamPred' (Maybe v) v
-- 'Found' ('IsTC' ''Just'') :: 'Predicate' (Maybe v)
-- @
--
-- @since 0.1.5.0
type IsTC t = EqBy (TyCon1 t)

-- | Convert a normal '->' type constructor taking two arguments into
-- a 'ParamPred'.
--
-- @
-- 'TyPP' :: (k -> v -> 'Type') -> 'ParamPred' k v
-- @
--
-- @since 0.1.4.0
data TyPP :: (k -> v -> Type) -> ParamPred k v
type instance Apply (TyPP t k) v = t k v

-- | Pre-compose a function to a 'ParamPred'.  Is essentially @'flip'
-- ('.')@, but unfortunately defunctionalization doesn't work too well with
-- that definition.
data PPMap :: (k ~> j) -> ParamPred j v -> ParamPred k v
type instance Apply (PPMap f p x) y = p (f @@ x) @@ y

-- | Pre-compose a function to a 'ParamPred', but on the "value" side.
--
-- @since 0.1.5.0
data PPMapV :: (u ~> v) -> ParamPred k u -> ParamPred k v
type instance Apply (PPMapV f p x) y = p x @@ (f @@ y)

instance (Decidable (Found (p :: ParamPred j v)), SingI (f :: k ~> j)) => Decidable (Found (PPMap f p)) where
    decide = mapDecision (\case i :&: p -> i :&: p)
                         (\case i :&: p -> i :&: p)
           . decide @(Found p)
           . applySing (sing :: Sing f)     -- can just be sing @f in singletons 2.5, ghc 8.6+

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
-- Because this is ambiguously typed, it must be called by applying the
-- 'ParamPred':
--
-- @
-- 'search' \@p
-- @
--
-- See 'searchTC' and 'SearchableTC' for a version that isn't ambiguously
-- typed, but only works when @p@ is a type constructor.
search
    :: forall p. Searchable p
    => Decide (Found p)
search = decide @(Found p)

-- | The proving/selecting function for @'Selectable' p@.
--
-- Because this is ambiguously typed, it must be called by applying the
-- 'ParamPred':
--
-- @
-- 'select' \@p
-- @
--
-- See 'selectTC' and 'SelectableTC' for a version that isn't ambiguously
-- typed, but only works when @p@ is a type constructor.
select
    :: forall p. Selectable p
    => Prove (Found p)
select = prove @(Found p)

-- | If @T :: k -> v -> 'Type'@ is a type constructor, then @'SearchableTC'
-- T@ is a constraint that @T@ is "searchable", in that you have
-- a canonical function:
--
-- @
-- 'searchTC' :: 'Sing' x -> 'Decision' (Σ v ('TyPP' T x))
-- @
--
-- That, given an @x :: k@, we can decide whether or not a @y :: v@ exists
-- that satisfies @T x y@.
--
-- Is essentially 'Searchable', except with /type constructors/ @k ->
-- 'Type'@ instead of matchable type-level functions (that are @k ~>
-- 'Type'@).  Useful because 'searchTC' doesn't require anything fancy like
-- TypeApplications to use.
--
-- @since 0.1.4.0
type SearchableTC t = Decidable (Found (TyPP t))

-- | If @T :: k -> v -> 'Type'@ is a type constructor, then @'Selectable'
-- T@ is a constraint that @T@ is "selectable", in that you have
-- a canonical function:
--
-- @
-- 'selectTC' :: 'Sing' a -> Σ v ('TyPP' T x)
-- @
--
-- That is, given an @x :: k@, we can /always/ find a @y :: k@ that
-- satisfies @T x y@.
--
-- Is essentially 'Selectable', except with /type constructors/ @k ->
-- 'Type'@ instead of matchable type-level functions (that are @k ~>
-- 'Type'@). Useful because 'selectTC' doesn't require anything fancy like
-- TypeApplications to use.
--
-- @since 0.1.4.0
type SelectableTC t = Provable  (Found (TyPP t))

-- | The canonical selecting function for @'Searchable' t@.
--
-- Note that because @t@ must be an injective type constructor, you can use
-- this without explicit type applications; the instance of 'SearchableTC'
-- can be inferred from the result type.
--
-- @since 0.1.4.0
searchTC
    :: forall t. SearchableTC t
    => Decide (Found (TyPP t))
searchTC = search @(TyPP t)

-- | The canonical selecting function for @'SelectableTC' t@.
--
-- Note that because @t@ must be an injective type constructor, you can use
-- this without explicit type applications; the instance of 'SelectableTC'
-- can be inferred from the result type.
--
-- @since 0.1.4.0
selectTC
    :: forall t. SelectableTC t
    => Prove (Found (TyPP t))
selectTC = select @(TyPP t)

-- | A @'ParamPred' (f k) k@.  Parameterized on an @as :: f k@, returns
-- a predicate that is true if there exists any @a :: k@ in @as@.
--
-- Essentially 'NotNull'.
type InP f = (ElemSym1 f :: ParamPred (f k) k)

-- | @'NotNull' f@ is basically @'Found' ('InP' f)@.
--
-- @since 0.1.2.0
notNullInP :: NotNull f --> Found (InP f)
notNullInP _ (WitAny i s) = s :&: i

-- | @'NotNull' f@ is basically @'Found' ('InP' f)@.
--
-- @since 0.1.2.0
inPNotNull :: Found (InP f) --> NotNull f
inPNotNull _ (s :&: i) = WitAny i s

instance Universe f => Decidable (Found (InP f)) where
    decide = mapDecision (\case WitAny i s -> s :&: i    )
                         (\case s :&: i     -> WitAny i s)
           . decide @(NotNull f)

instance Decidable (NotNull f ==> Found (InP f))
instance Provable (NotNull f ==> Found (InP f)) where
    prove = notNullInP

instance Decidable (Found (InP f) ==> NotNull f)
instance Provable (Found (InP f) ==> NotNull f) where
    prove = inPNotNull

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
    decide = mapDecision (\case WitAny i (x :&: p) -> x :&: WitAny i p  )
                         (\case x :&: WitAny i p   -> WitAny i (x :&: p))
           . decide @(Any f (Found p))

-- | Disjunction on two 'ParamPred's, with appropriate 'Searchable'
-- instance.  Priority is given to the left predicate.
--
-- @since 0.1.3.0
data OrP :: ParamPred k v -> ParamPred k v -> ParamPred k v
type instance Apply (OrP p q x) y = (p x ||| q x) @@ y

-- | Conjunction on two 'ParamPred's, with appropriate 'Searchable' and
-- 'Selectable' instances.
--
-- @since 0.1.3.0
data AndP :: ParamPred k v -> ParamPred k u -> ParamPred k (v, u)
type instance Apply (AndP p q x) '(y, z) = (p x @@ y, q x @@ z)

instance (Searchable p, Searchable q) => Decidable (Found (OrP p q)) where
    decide x = case search @p x of
      Proved (s :&: p) -> Proved $ s :&: Left p
      Disproved vp     -> case search @q x of
        Proved (s :&: q) -> Proved $ s :&: Right q
        Disproved vq     -> Disproved $ \case
          s :&: Left  p -> vp (s :&: p)
          s :&: Right q -> vq (s :&: q)

instance (Searchable p, Searchable q) => Decidable (Found (AndP p q)) where
    decide x = case search @p x of
      Proved (s :&: p) -> case search @q x of
        Proved (t :&: q) -> Proved $ STuple2 s t :&: (p, q)
        Disproved vq     -> Disproved $ \case
          STuple2 _ t :&: (_, q) -> vq $ t :&: q
      Disproved vp     -> Disproved $ \case
        STuple2 s _ :&: (p, _) -> vp $ s :&: p

instance (Selectable p, Selectable q) => Provable (Found (AndP p q)) where
    prove x = case select @p x of
        s :&: p -> case select @q x of
          t :&: q -> STuple2 s t :&: (p, q)
