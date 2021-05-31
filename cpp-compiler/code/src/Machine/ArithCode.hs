module Machine.ArithCode where

import Syntax        ( ArithOp(..) )
import Machine.Code  ( Size(..), Code, Location(..), Instruction(..), Value(..)
                     , Register(..), RegName(..)
                     , locToValue, mkInst
                     , r11d, eax, edx, mov
                     )
import Machine.Monad ( Machine, icRegToLoc, icOpToValue )
import qualified InterCode as IC ( Operand, Register )

import Control.Arrow       ( (***) )
import Control.Applicative ( (<$>) )

arithCodeNeg :: IC.Operand -> IC.Register -> Machine Code
arithCodeNeg val r = (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
                     (map mkInst *** id) <$> icOpToValue val >>= \(valic,mval) ->
                     return $ valic ++ locic ++
                     map mkInst ( mov Long mval eax ++
                                  [ NEG Long eax ] ++
                                  mov Long (locToValue eax) loc
                                )
    
arithCode :: ArithOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
arithCode aop v1 v2 r = 
    (map mkInst *** id) <$> icOpToValue v1 >>= \(v1ic,mval1) ->
    (map mkInst *** id) <$> icOpToValue v2 >>= \(v2ic,mval2) ->
    (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
    return $ v1ic ++ v2ic ++ locic ++
    case aop of
        Plus -> arithCode' (ADD Long mval2 eax) mval1 loc
        Min  -> arithCode' (SUB Long mval2 eax) mval1 loc
        Prod -> arithCode' (IMUL Long mval2 (R Long RAX)) mval1 loc
        Div  -> divisionCode (mov Long (locToValue eax) loc) mval1 mval2
        Mod  -> divisionCode (mov Long (locToValue edx) loc) mval1 mval2

divisionCode :: [Instruction] -> Value -> Value -> Code
divisionCode insts mv1 mv2 =
    map mkInst $ 
    mov Long mv1 eax ++
    mov Long mv2 r11d ++
    [ CLTD
    , DIVL r11d
    ] ++ 
    insts
    
arithCode' :: Instruction -> Value -> Location -> Code
arithCode' inst mv loc = 
    map mkInst $
    mov Long mv eax ++ 
    [ inst ] ++
    mov Long (locToValue eax) loc


