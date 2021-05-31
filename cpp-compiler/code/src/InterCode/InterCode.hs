{-# Language TypeSynonymInstances, FlexibleInstances #-}
module InterCode.InterCode where

import Syntax

data Label = L (String,Int)

type Register = Int

type Size = Integer

data Operand = R Register
             | C Literal
    deriving Show
                -- Las variables globales comienzan en el registro cero.
data InterCode' = StoreG [(Type,Size)] 
                | Store  Register [(Type,Size)]
                -- {a[e'] = e} ===> AssignArray {e} {e'} {a}
                | AssignArray Operand Operand Register
                | BAssign BinOp Operand Operand Register
                | UAssign UnOp Operand Register
                -- {a = b} ===> ICAssign {b} {a}
                | ICAssign Operand Register
                -- {l = a[e]} ===> ICArrAssign {a} {e} {l}
                | ICArrAssign Register Operand Register
                -- Movemos un registro al "lugar" de retorno
                | PutReturn Register
                -- Movemos del "lugar" de retorno a un registro
                | PopReturn Register
                | Call Label [Operand]
                | CallE Label [Operand]
                | PopParams [Register]
                | Jump Label
                | JumpCnd Operand Label Label
                | ICReturn
                | ICSkip
    deriving Show

type InterCode = [(Label,InterCode')]

instance Show Label where
    show (L (l,n)) | length l == 0 = ""
                   | otherwise     = let strn = if n < 1 then "" else show n
                                     in l ++ strn

unwrapLabel :: Label -> (String, Int)
unwrapLabel (L si) = si

stickLabel :: Label -> InterCode -> InterCode
stickLabel _ [] = []
stickLabel l ((_,ic'):ics) = (l,ic'):ics

neutralLabel :: Label
neutralLabel = L ("",0)

icodeNoLabel :: InterCode' -> InterCode
icodeNoLabel ic = [(neutralLabel,ic)]

stringToLabel :: String -> Label
stringToLabel str = L (str,-1)

-- Registro especial para el valor de retorno:
returnRegister :: Register
returnRegister = 0

nextRegister :: Register -> Register
nextRegister = (+1)
