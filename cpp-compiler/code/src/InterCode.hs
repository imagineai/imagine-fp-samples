module InterCode ( generateInterCode
                 , pprintInterCode
                 , module InterCode.InterCode
                 ) where

import InterCode.Monad     ( IC, ICState, emptyICR, emptyICS )
import InterCode.Program   ( interCodeFromClass )
import InterCode.InterCode

import StaticCheck.TypeChecker.TypedSyntax ( TypedProgram )

import Control.Monad.RWS ( runRWS )

generate :: TypedProgram -> (InterCode, ICState, ())
generate p = runRWS (genInterCode p) emptyICR emptyICS

generateInterCode :: TypedProgram -> InterCode
generateInterCode p = case generate p of
                           (ic,_,_) -> ic

genInterCode :: TypedProgram -> IC InterCode
genInterCode []  = return []
genInterCode [c] = interCodeFromClass c
genInterCode _  = error "No implementado"

pprintInterCode :: InterCode -> String
pprintInterCode = unlines . map pprint'

pprintLabel :: Label -> String
pprintLabel (L (l,n)) = let whites = replicate (15 - length l) ' '
                            strn   = if n < 1 then ": " else show n ++ ": "
                        in if null l
                           then whites
                           else l ++ strn ++ drop (length strn) whites

pprint' :: (Label,InterCode') -> String
pprint' (l,ic') =  pprintLabel l ++ show ic'
