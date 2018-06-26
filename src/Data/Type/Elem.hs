{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Elem (
    Universe(..)
  , Any(..), All(..)
  , entailAny, entailAll
  , Index(..)
  , IsJust(..)
  , NEIndex(..)
  , Snd(..)
  ) where

import           Data.Kind
import           Data.List.NonEmpty                    (NonEmpty(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding        (Any, All, Snd, Elem)
import           Prelude hiding                        (any, all)
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

type family Elem (f :: Type -> Type) :: f k -> k -> Type

data Any :: (k ~> Type) -> f k -> Type where
    Any :: Elem f as a -> p @@ a -> Any p as

newtype All p (as :: f k) = All { runAll :: forall a. Elem f as a -> p @@ a }

class Universe (f :: Type -> Type) where

    any :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)

    all :: forall k (p :: k ~> Type) (as :: f k). ()
        => (forall a. Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)

    select :: Elem f as a -> Sing as -> Sing a

entailAny
    :: forall p q as. ()
    => (forall a. p @@ a -> q @@ a)
    -> Any p as
    -> Any q as
entailAny f = \case
    Any (i :: Elem f as a) (x :: p @@ a) -> Any i (f @a x)

entailAll
    :: forall p q as. ()
    => (forall a. p @@ a -> q @@ a)
    -> All p as
    -> All q as
entailAll f a = All $ \(i :: Elem f as a) -> f @a (runAll a i)

data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

type instance Elem [] = Index

instance Universe [] where

    any :: forall k (p :: k ~> Type) (as :: [k]). ()
        => (forall a. Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)
    any f = go
      where
        go :: Sing bs -> Decision (Any p bs)
        go = \case
          SNil -> Disproved $ \case
            Any i _ -> case i of {}
          x `SCons` xs -> case f x of
            Proved p    -> Proved $ Any IZ p
            Disproved v -> case go xs of
              Proved (Any i p) -> Proved $ Any (IS i) p
              Disproved vs -> Disproved $ \case
                Any IZ     p -> v p
                Any (IS i) p -> vs (Any i p)

    all :: forall k (p :: k ~> Type) (as :: [k]). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (All p as)
    all f = go
      where
        go :: Sing bs -> Decision (All p bs)
        go = \case
          SNil -> Proved $ All $ \case {}
          x `SCons` xs -> case f x of
            Proved p -> case go xs of
              Proved a -> Proved $ All $ \case
                IZ   -> p
                IS i -> runAll a i
              Disproved v -> Disproved $ \a -> v $ All (runAll a . IS)
            Disproved v -> Disproved $ \a -> v $ runAll a IZ

    select = \case
      IZ -> \case
        x `SCons` _  -> x
      IS i -> \case
        _ `SCons` xs -> select i xs

data IsJust :: Maybe k -> k -> Type where
    IsJust :: IsJust ('Just a) a

type instance Elem Maybe = IsJust

instance Universe Maybe where
    any f = \case
      SNothing -> Disproved $ \case Any i _ -> case i of {}
      SJust x  -> case f x of
        Proved p    -> Proved $ Any IsJust p
        Disproved v -> Disproved $ \case
          Any IsJust p -> v p

    all f = \case
      SNothing -> Proved $ All $ \case {}
      SJust x  -> case f x of
        Proved p    -> Proved $ All $ \case IsJust -> p
        Disproved v -> Disproved $ \a -> v $ runAll a IsJust

    select = \case
      IsJust -> \case
        SJust x -> x

data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

type instance Elem NonEmpty = NEIndex

instance Universe NonEmpty where
    any :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (Any p as)
    any f (x NE.:%| xs) = case f x of
      Proved p    -> Proved $ Any NEHead p
      Disproved v -> case any @_ @_ @p f xs of
        Proved (Any i p) -> Proved $ Any (NETail i) p
        Disproved vs     -> Disproved $ \case
          Any i p -> case i of
            NEHead    -> v p
            NETail i' -> vs (Any i' p)

    all :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
        => (forall a. Sing a -> Decision (p @@ a))
        -> Sing as
        -> Decision (All p as)
    all f (x NE.:%| xs) = case f x of
      Proved p -> case all @_ @_ @p f xs of
        Proved ps -> Proved $ All $ \case
          NEHead   -> p
          NETail i -> runAll ps i
        Disproved v -> Disproved $ \a -> v $ All (runAll a . NETail)
      Disproved v -> Disproved $ \a -> v $ runAll a NEHead

    select = \case
      NEHead   -> \case
        x NE.:%| _  -> x
      NETail i -> \case
        _ NE.:%| xs -> select i xs

data Snd :: (j, k) -> k -> Type where
    Snd :: Snd '(a, b) b

type instance Elem ((,) j) = Snd

instance Universe ((,) j) where
    any f (STuple2 _ x) = case f x of
      Proved p    -> Proved $ Any Snd p
      Disproved v -> Disproved $ \case Any Snd p -> v p

    all f (STuple2 _ x) = case f x of
      Proved p    -> Proved $ All $ \case Snd -> p
      Disproved v -> Disproved $ \a -> v $ runAll a Snd

    select = \case
      Snd -> \case
        STuple2 _ x -> x
