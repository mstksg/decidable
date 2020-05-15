{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Data.Type.Predicate.TH
-- License     : BSD3
-- Copyright   : (c) Evgeny Poberezkin 2020
--
-- Maintainer  : evgeny@poberezkin.com
-- Stability   : experimental
-- Portability : non-portable
--
-- Template Haskell to generate instances of Auto typeclass for
-- parametrized type constructor.
module Data.Type.Predicate.TH (
  autoI
  ) where

import Data.Type.Predicate
import Data.Type.Predicate.Auto
import Language.Haskell.TH

-- | Generate instances of 'Auto' typeclass for a given parametrised type definition,
-- keeping the type definition.
--
-- Given type definitions (with splice quasiquote uncommented):
--
-- @
-- data P = A | B | C
--
-- -- $(autoI [d|
--   data T (a :: P) where
--     TA :: T 'A
--     TB :: T 'B
-- --  |])
-- @
--
-- these instances will be added:
--
-- @
-- instance Auto (TyPred T) 'A where auto = TA
-- instance Auto (TyPred T) 'B where auto = TB
-- @
--
-- These instances are only needed for contexts, 'autoTC' will work without them.
autoI :: Q [Dec] -> Q [Dec]
autoI decls = concat <$> (decls >>= mapM addInstances)
  where
    addInstances :: Dec -> Q [Dec]
    addInstances d@(DataD _ _ _ _ constructors _) = do
      ds <- mapM mkInstance constructors
      if any null ds then do
        reportWarning $
          "warning: not a parametrised GADT (no instances added)\n" ++ pprint d
        return [d]
      else
        return $ d : concat ds
    addInstances d = do
      reportWarning $ "warning: not a data type declaration\n" ++ pprint d
      return [d]

    mkInstance :: Con -> Q [Dec]
    mkInstance (GadtC [con] _ (AppT (ConT ty) (PromotedT p))) =
      [d|
        instance Auto (TyPred $(conT ty)) $(promotedT p) where
          auto = $(conE con)
        |]
    mkInstance _ = return []
