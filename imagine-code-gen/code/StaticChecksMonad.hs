{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

{-|
Module      : StaticChecks.StaticChecksMonad
Description : Generic monad for all static checks.
Copyright   : (c) 2020-2021 Imagine AI
License     : BSD-3-Clause
Maintainer  : sos@imagine.ai
Stability   : develop

-}

module StaticChecks.StaticChecksMonad where

-- External imports
import Control.Arrow ( second )
import Control.Monad.Writer ( tell )
import Control.Monad.RWS ( MonadRWS, runRWST )
import Control.Monad.Except ( MonadError, runExcept, throwError )
import Data.Function ( on )
import Data.Text ( Text )
import qualified Control.Monad.Reader as Reader ( asks, local, reader )
import qualified Data.List.NonEmpty as NE ( fromList )


-- Internal imports
import ImagineSettings ( Settings, isAPIGraphQL, isFWDjango )
import ImagineError  ( StaticError, StaticWarning
                     , StaticErrors (StaticErrors), StaticWarnings
                     )
import ImagineSpec.Annotation ( Annotation )
import Casing

data SCheckReader = SCheckReader { config :: Settings
                                 , casing :: Casing
                                 }

-- | General monad for the static checks.
type SCheckMonad r s a = forall m.
                         ( MonadRWS (SCheckReader, r) StaticWarnings s m
                         , MonadError StaticErrors m
                         ) => m a

-- | Main run function for static checks.
runSCheck :: Casing -> Settings -> r -> s -> SCheckMonad r s a ->
             Either StaticErrors StaticWarnings
runSCheck cas conf r s check = runExcept $ runRWST check (casconf, r) s >>=
                               \(_,_,ws) -> return ws
  where casconf = SCheckReader { config = conf
                               , casing = cas
                               }

-- | Report errors.
throwCheckError :: Annotation -> StaticError -> SCheckMonad r s a
throwCheckError a e = throwError . StaticErrors . NE.fromList . pure $ (a, e)

-- | Report warnings.
warning :: Annotation -> StaticWarning -> SCheckMonad r s ()
warning an sw = tell [(an, sw)]

-- | Ask for the imagine spec configuration.
askConfig :: SCheckMonad r s Settings
askConfig = Reader.asks (config . fst)

-- | Ask for the casing.
askCasing :: SCheckMonad r s Casing
askCasing = Reader.asks (casing . fst)

askIsAPIGraphQL :: SCheckMonad r s Bool
askIsAPIGraphQL = isAPIGraphQL <$> askConfig

askIsFWDjango :: SCheckMonad r s Bool
askIsFWDjango = isFWDjango <$> askConfig

-- | Redefined reader functionality. We must always use these versions for the
--   static checks.
ask :: SCheckMonad r s r
ask = Reader.asks snd

local :: (r -> r) -> SCheckMonad r s a -> SCheckMonad r s a
local f = Reader.local (second f)

asks :: (r -> a) -> SCheckMonad r s a
asks f = Reader.asks (f . snd)

reader :: (r -> a) -> SCheckMonad r s a
reader f = Reader.reader (f . snd)

-- Usefull functions for static checks.

maybeM_ :: Monad m => (a -> m ()) -> Maybe a -> m ()
maybeM_ = maybe $ return ()

findDup :: Eq b => (b -> [b] -> Bool) -> (a -> b) -> [a] -> Maybe a
findDup cmp = findDup' []
  where
    findDup' seen f (x:xs) = if f x `cmp` seen
                             then Just x
                             else findDup' (f x:seen) f xs
    findDup' _ _ [] = Nothing

casingElem :: CasingFun -> Text -> [Text] -> Bool
casingElem cf = any . ((==) `on` cf)
