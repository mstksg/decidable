{-# LANGUAGE LambdaCase      #-}
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
-- Template Haskell to generate Auto typeclass instances for
-- parametrized type.
module Data.Type.Predicate.TH (
  -- * Generate Auto typeclass instances
  autoI
  , getAutoI
  ) where

import Data.Type.Predicate
import Data.Type.Predicate.Auto
import Language.Haskell.TH

-- | Generate instances of 'Auto' typeclass for a given parametrised type definition,
-- keeping the type definition.
--
-- Given type definitions:
--
-- > data P = A | B | C
-- >
-- > $(autoI [d|
-- >   data T (a :: P) where
-- >     TA :: T 'A
-- >     TB :: T 'B
-- >   |])
--
-- these instances will be added:
--
-- > instance Auto (TyPred T) 'A where auto = TA
-- > instance Auto (TyPred T) 'B where auto = TB
--
-- These instances are only needed for contexts, 'autoTC' will work without them.
autoI :: Q [Dec] -> Q [Dec]
autoI decls = concat <$> (decls >>= mapM addInstances)
  where
    addInstances :: Dec -> Q [Dec]
    addInstances d = (d:) <$> mkInstances d

-- | Generate instances of Auto typeclass for each of the provided type 'Name's
--
-- Instead of wrapping type declarations in 'autoI', you can pass type names to
-- this function:
--
-- > $(getAutoI [''T])
getAutoI :: [Name] -> Q [Dec]
getAutoI names = concat <$> mapM mkTypeInstances names
  where
    mkTypeInstances :: Name -> Q [Dec]
    mkTypeInstances name =
      reify name >>= \case
        TyConI d -> mkInstances d
        _ -> do
          reportError $ "error: not a type constructor\n" ++ pprint name
          return []

mkInstances :: Dec -> Q [Dec]
mkInstances d@(DataD _ _ _ _ constructors _) = do
  ds <- mapM mkInstance constructors
  if any null ds then do
    reportWarning $
      "warning: not a parametrised GADT (no instances added)\n" ++ pprint d
    return []
  else
    return $ concat ds
mkInstances d = do
  reportWarning $ "warning: not a data type declaration\n" ++ pprint d
  return []

mkInstance :: Con -> Q [Dec]
mkInstance (GadtC [con] _ (AppT (ConT ty) (PromotedT p))) =
  [d|
    instance Auto (TyPred $(conT ty)) $(promotedT p) where
      auto = $(conE con)
    |]
mkInstance _ = return []
