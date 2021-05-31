module StaticCheck.Generic 
       ( module StaticCheck.Generic.Error
       , module StaticCheck.Generic.Monad
       , module StaticCheck.Generic.Checks
       )
       where


import StaticCheck.Generic.Error  ( GenericErrors )
import StaticCheck.Generic.Monad  ( initGReader, initGState )
import StaticCheck.Generic.Checks ( genericChecksProgram, checkErrors )
