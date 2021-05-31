module StaticCheck ( GenericErrors , TCError
                   , TypedProgram
                   , typecheckProgram
                   , genericChecks
                   , pprintTyProgram
                   ) where

import Syntax ( Program )

import StaticCheck.TypeChecker ( pprintTyProgram, checkProgram
                               , emptyLocalCtx, emptyTCState
                               , TCError, TypedProgram
                               )
import StaticCheck.Generic     ( genericChecksProgram, checkErrors
                               , initGReader, initGState
                               , GenericErrors
                               )

import Control.Monad.RWS   ( runRWST, runRWS )
import Control.Applicative ((<$>))

typecheckProgram :: Program -> Either TCError TypedProgram
typecheckProgram p = (\(tp,_,_) -> tp) <$> 
                     runRWST (checkProgram p) emptyLocalCtx emptyTCState

genericChecks :: Program -> GenericErrors
genericChecks p = 
         let (_,gs,_) = runRWS (genericChecksProgram p) initGReader initGState
         in checkErrors gs
