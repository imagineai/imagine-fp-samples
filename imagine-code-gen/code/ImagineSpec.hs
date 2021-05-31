{-|
Module      : ImagineSpec
Description : Abstraction of a Imagine specification.
Copyright   : (c) 2020-2021 Imagine AI
License     : BSD-3-Clause
Maintainer  : sos@imagine.ai
Stability   : develop

-}

module ImagineSpec (
  -- * Imagen specification type.
    ImagineSpec(..)
  , module ImagineSpec.DataModelSpec
  , module ImagineSpec.APISpec
  , module ImagineSpec.AuthoSpec
  , module ImagineSpec.StorageSpec
  , module ImagineSpec.CustomErrorSpec
  , module ImagineSettings
  , module ImagineSpec.Providers

  -- * Smart constructor
  , createImagineSpec
  , defaultImagineSpec

  -- * Queries
  , imGetCasing
  , imProjectName
  , noModels
  ) where


-- Internal imports
import ImagineSettings
import ImagineSpec.Providers
import ImagineSpec.APISpec
import ImagineSpec.AuthoSpec
import ImagineSpec.DataModelSpec
import ImagineSpec.StorageSpec
import ImagineSpec.CustomErrorSpec
import Casing
import Casing.Django
import Casing.Node

data ImagineSpec = ImagineSpec { settings        :: !Settings
                               , providerSpec    :: !ProviderSpec
                               , modelSpec       :: !DataModelSpec
                               , authoSpec       :: !AuthoSpec
                               , apiSpec         :: !APISpec
                               , storageSpec     :: !StorageSpec
                               , customErrorSpec :: !CustomErrorSpec
                               }
  deriving Show

createImagineSpec :: Settings -> DataModelSpec -> AuthoSpec -> APISpec ->
                     StorageSpec -> CustomErrorSpec -> ProviderSpec ->
                                                       ImagineSpec
createImagineSpec set ms as apis stg ces pspec = ImagineSpec
  { settings        = set
  , modelSpec       = ms
  , authoSpec       = as
  , apiSpec         = apis
  , storageSpec     = stg
  , customErrorSpec = ces
  , providerSpec    = pspec
  }

defaultImagineSpec :: Settings -> ImagineSpec
defaultImagineSpec set = createImagineSpec
  set
  emptyDataModelSpec
  emptyAuthoSpec
  emptyAPISpec
  (defaultStorageSpec $ projectName set)
  emptyCustomErrorSpec
  emptyProviderSpec

imProjectName :: ImagineSpec -> ProjectName
imProjectName = projectName . settings

imGetCasing :: ImagineSpec -> Casing
imGetCasing is | isFWDjango (settings is) = djangoCasing
               | isFWNode (settings is)   = nodeCasing
               | otherwise = error "cannot get casing"

noModels :: ImagineSpec -> Bool
noModels = null . models . modelSpec
