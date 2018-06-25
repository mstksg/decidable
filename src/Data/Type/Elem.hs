{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Elem (
    Elem
  , Any(..), Search(..)
  , All(..), Verify(..)
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
import qualified Data.Singletons.Prelude.List.NonEmpty as NE

type family Elem (f :: Type -> Type) :: f k -> k -> Type

data Any p as where
    Any :: Elem f as a
        -> p @@ a
        -> Any p as

class Search f where
    search :: forall k (p :: k ~> Type) (as :: f k). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (Any p as)


newtype All p (as :: f k) = All { runAll :: forall a. Elem f as a -> p @@ a }

class Verify f where
    verify :: forall k (p :: k ~> Type) (as :: f k). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (All p as)

data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

type instance Elem [] = Index

instance Search [] where
    search :: forall k (p :: k ~> Type) (as :: [k]). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (Any p as)
    search f = go
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

instance Verify [] where
    verify :: forall k (p :: k ~> Type) (as :: [k]). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (All p as)
    verify f = go
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

data IsJust :: Maybe k -> k -> Type where
    IsJust :: IsJust ('Just a) a

type instance Elem Maybe = IsJust

instance Search Maybe where
    search f = \case
      SNothing -> Disproved $ \case Any i _ -> case i of {}
      SJust x  -> case f x of
        Proved p    -> Proved $ Any IsJust p
        Disproved v -> Disproved $ \case
          Any IsJust p -> v p

instance Verify Maybe where
    verify f = \case
      SNothing -> Proved $ All $ \case {}
      SJust x  -> case f x of
        Proved p    -> Proved $ All $ \case IsJust -> p
        Disproved v -> Disproved $ \a -> v $ runAll a IsJust

data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

type instance Elem NonEmpty = NEIndex

instance Search NonEmpty where
    search :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (Any p as)
    search f (x NE.:%| xs) = case f x of
      Proved p    -> Proved $ Any NEHead p
      Disproved v -> case search @_ @_ @p f xs of
        Proved (Any i p) -> Proved $ Any (NETail i) p
        Disproved vs     -> Disproved $ \case
          Any i p -> case i of
            NEHead    -> v p
            NETail i' -> vs (Any i' p)

instance Verify NonEmpty where
    verify :: forall k (p :: k ~> Type) (as :: NonEmpty k). ()
           => (forall a. Sing a -> Decision (p @@ a))
           -> Sing as
           -> Decision (All p as)
    verify f (x NE.:%| xs) = case f x of
      Proved p -> case verify @_ @_ @p f xs of
        Proved ps -> Proved $ All $ \case
          NEHead   -> p
          NETail i -> runAll ps i
        Disproved v -> Disproved $ \a -> v $ All (runAll a . NETail)
      Disproved v -> Disproved $ \a -> v $ runAll a NEHead

data Snd :: (j, k) -> k -> Type where
    Snd :: Snd '(a, b) b

type instance Elem ((,) j) = Snd

instance Search ((,) j) where
    search f (STuple2 _ x) = case f x of
      Proved p    -> Proved $ Any Snd p
      Disproved v -> Disproved $ \case Any Snd p -> v p

instance Verify ((,) j) where
    verify f (STuple2 _ x) = case f x of
      Proved p    -> Proved $ All $ \case Snd -> p
      Disproved v -> Disproved $ \a -> v $ runAll a Snd
