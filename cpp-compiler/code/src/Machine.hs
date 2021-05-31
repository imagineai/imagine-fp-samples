module Machine ( generateAssembly
               , pprintCode
               ) where

import Machine.Code    ( Code )
import Machine.Monad   ( Header, header, emptyMState )
import Machine.PPrint  ( pprintCode )
import Machine.GenCode ( genCode )

import qualified InterCode as IC ( InterCode )

import Control.Monad.State ( runState )
import Control.Arrow       ( second )

generateAssembly :: IC.InterCode -> (Code,Header)
generateAssembly ic = second header $ runState (genCode ic) emptyMState
