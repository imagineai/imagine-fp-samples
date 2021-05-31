{-# Language DeriveDataTypeable #-}
module MainHandler.Exceptions where

import StaticCheck ( GenericErrors, TCError )

import Data.Typeable     ( Typeable  )
import Control.Exception ( Exception )

import Text.Parsec ( ParseError )

data MainExceptions = ParserE    ParseError
                    | GenericE   GenericErrors
                    | TypeCheckE TCError
    deriving (Show, Typeable)

instance Exception MainExceptions
