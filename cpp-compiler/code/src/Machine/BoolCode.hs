module Machine.BoolCode where

import Syntax        ( RelOp(..), EqOp(..), CondOp(..), Type(..) )
import Machine.Code  ( Size(..), Code, Location(..), Instruction(..), Value(..)
                     , CmpFlags(..)
                     , locToValue, mkInst
                     , al, eax, mov
                     )
import Machine.Monad ( Machine, icRegToLoc, icOpToValue, icOpToType )
import qualified InterCode as IC ( Operand, Register )

import Control.Arrow       ( (***) )
import Control.Applicative ( (<$>) )

boolCodeNot :: IC.Operand -> IC.Register -> Machine Code
boolCodeNot val r = (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
                    (map mkInst *** id) <$> icOpToValue val >>= \(valic,mval) ->
                    return $ valic ++ locic ++
                    map mkInst ( mov Byte mval eax ++
                                 [ CMP Byte (C 0) mval
                                 , SET E al
                                 ] ++
                                 mov Byte (locToValue al) loc
                               )

boolCodeRel :: RelOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
boolCodeRel rop v1 v2 r =
    let set = case rop of
                Lt -> SET L
                Gt -> SET G
                Leq -> SET LE
                Geq -> SET GE
    in
        (map mkInst *** id) <$> icOpToValue v1 >>= \(v1ic,mval1) ->
        (map mkInst *** id) <$> icOpToValue v2 >>= \(v2ic,mval2) -> 
        (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
        return $ v1ic ++ v2ic ++ locic ++
        map mkInst ( mov Long mval1 eax ++ 
                     [ CMP Long mval2 (Loc eax)
                     , set al
                     ] ++
                     mov Byte (locToValue al) loc
                   )

boolCodeEq :: EqOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
boolCodeEq eop v1 v2 r =
    icOpToType v1 >>= \ty ->
    case ty of
         BoolType -> boolCodeEqBool eop v1 v2 r
         IntType -> boolCodeEqInt eop v1 v2 r
         _ -> error "solo implementado para Int y BooL"

boolCodeEqBool :: EqOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
boolCodeEqBool = boolCodeEq' Byte al

boolCodeEqInt :: EqOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
boolCodeEqInt = boolCodeEq' Long eax

boolCodeEq' :: Size -> Location -> EqOp -> IC.Operand -> IC.Operand -> 
               IC.Register -> Machine Code
boolCodeEq' size mr eop v1 v2 r =
    let set = case eop of
                Equal -> SET E
                NEqual -> SET NE
    in
        (map mkInst *** id) <$> icOpToValue v1 >>= \(v1ic,mval1) ->
        (map mkInst *** id) <$> icOpToValue v2 >>= \(v2ic,mval2) ->
        (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
        return $ v1ic ++ v2ic ++ locic ++
        map mkInst ( mov size mval1 mr ++
                     [ CMP size mval2 (Loc mr)
                     , set al
                     ] ++
                     mov Byte (locToValue al) loc
                   )

boolCodeCond :: CondOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
boolCodeCond cop v1 v2 r =
    let inst = case cop of
                 And -> AND Byte
                 Or -> OR Byte
    in
        (map mkInst *** id) <$> icOpToValue v1 >>= \(v1ic,mval1) -> 
        (map mkInst *** id) <$> icOpToValue v2 >>= \(v2ic,mval2) ->
        (map mkInst *** id) <$> icRegToLoc r >>= \(locic,loc) ->
        return $ v1ic ++ v2ic ++ locic ++
        map mkInst ( mov Byte mval1 al ++
                     [ inst mval2 al ] ++
                     mov Byte (locToValue al) loc
                   )
