module StaticCheck.TypeChecker.Program where

import Syntax ( Program )

import StaticCheck.TypeChecker.Monad       ( TCheck )
import StaticCheck.TypeChecker.Class       ( checkClass )
import StaticCheck.TypeChecker.TypedSyntax ( TypedProgram )

import Control.Monad.RWS   ( forM )

checkProgram :: Program -> TCheck TypedProgram
checkProgram = flip forM checkClass
