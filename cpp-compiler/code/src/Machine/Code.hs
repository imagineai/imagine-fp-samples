module Machine.Code where

import Syntax ( Type (..) )
    
data RegName = 
             RAX
           | RBX
           | RCX
           | RDX
           | RSI
           | RDI
           | RSP
           | RBP
           | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
    deriving (Show,Eq)
    
    
data Register = R Size RegName
    deriving Show

data Size = Byte | Word | Long | Quad
    deriving Show
    
-- Direcciones de memoria relativas al valor de un registro
data MemAddress = MAddr Integer Register
    deriving Show
    
-- -48(%rbp,%rax,4) correspone a MemArr -48 RAX Long
data MemArray = MemArr MemAddress Register Size
    
data Mem = MAdd MemAddress | MAR MemArray
    
data Location =  MA Mem | Reg Register

data Value = C Integer | Loc Location | Str Label
    
type Label = String
    
-- Tipo para el resultado de una comparación con CMP
data CmpFlags = E | NE | G | GE | L | LE
    
{- Conjunto de instrucciones del procesador x86_x64 que utilizaremos -}
data Instruction = MOV Size Value Location
                 | LEAQ MemAddress Register
                 | ADD Size Value Location
                 | SUB Size Value Location
                 | IMUL Size Value Register
                 | NEG Size Location
                   -- División con signo para enteros de 32 bits.
                 | DIVL Location
                   -- Algo para la division
                 | CLTD
                    -- Convierte el valor de EAX a Quad
                 | CLTQ
                    -- Booleanas. Los booleanos los representamos con 1 Byte.
                 | AND Size Value Location
                 | OR Size Value Location
                    -- Comparación
                 | CMP Size Value Value
                 | SET CmpFlags Location
                    -- Saltos
                 | J CmpFlags Label
                 | JMP Label
                    -- Instrucciones para manejo de stack y llamadas
                 | CALL Label
                 | ENTER Value Value
                 | SYSCALL
                 | LEAVE
                 | RET
                 | NOP
                 
type Code = [(Label,Instruction)]

-- Construye una instruccion sin label
mkInst :: Instruction -> (Label,Instruction)
mkInst i = ("",i)

locToValue :: Location -> Value
locToValue = Loc

minMAddr :: MemAddress -> Integer -> MemAddress
minMAddr (MAddr i r) i' = MAddr (i - i') r

-- Registro RAX de 4 bytes:
eax :: Location
eax = Reg $ R Long RAX

r11d :: Location
r11d = Reg $ R Long R11

-- Registro RAX de 1 byte:
al :: Location
al = Reg $ R Byte RAX

edx :: Location
edx = Reg $ R Long RDX

edi :: Location
edi = Reg $ R Long RDI

rsp :: Location
rsp = Reg $ R Quad RSP

rdi :: Location
rdi = Reg $ R Quad RDI

rax :: Location
rax = Reg $ R Quad RAX

r10 :: Location
r10 = Reg $ R Quad R10

-- Primer registro para pasaje de parámetro
fRegArg :: RegName
fRegArg = RDI

nextRegArg :: RegName -> RegName
nextRegArg RDI = RSI
nextRegArg RSI = RDX
nextRegArg RDX = RCX
nextRegArg RCX = R8
nextRegArg R8  = R9
nextRegArg rn  = error $ unwords [ "nextRegArg: No debería hacer falta"
                                 , "aplicar esta función a"
                                 , show rn
                                 ]

-- Primera posición de memoria p6ara pasaje de parámetro cuando
-- se superan los seis.
fMemArg :: MemAddress
fMemArg = MAddr 0 (R Quad RSP)

nextMemArg :: MemAddress -> MemAddress
nextMemArg (MAddr n r) = MAddr (n+8) r

selfAddr :: MemAddress
selfAddr = MAddr (-8) (R Quad RBP)

-- Para mover de memoria a memoria usamos arbitrariamente el registro 11
mov :: Size -> Value -> Location -> [Instruction]
mov size v@(Loc (MA _)) l@(MA _) = 
    [ MOV size v r11
    , MOV size (locToValue r11) l]
    where r11 :: Location
          r11 = Reg $ R size R11
mov size v loc = [ MOV size v loc ]

memArr :: MemAddress -> Register -> Size -> Mem
memArr ma r size = MAR (MemArr ma r size)

maToLoc :: MemAddress -> Location
maToLoc = MA . MAdd

typeToSize :: Type -> Size
typeToSize IntType    = Long
typeToSize BoolType   = Byte
typeToSize StringType = Long
typeToSize _ = error "no implementado para otro tipo"
