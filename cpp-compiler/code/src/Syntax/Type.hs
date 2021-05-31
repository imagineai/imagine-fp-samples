module Syntax.Type where

import Syntax.Expr ( Identifier )

data Type = IntType  | FloatType | BoolType | StringType 
          | VoidType | VType Identifier
     deriving Eq
     
     
-- Subtipado
isNum :: Type -> Bool
isNum IntType = True
isNum FloatType = True
isNum _ = False

subtype :: Type -> Type -> Maybe Type
subtype IntType IntType = Just IntType
subtype IntType FloatType = Just FloatType
subtype FloatType IntType = Just FloatType
subtype FloatType FloatType = Just FloatType
subtype _ _ = Nothing

instance Show Type where
    show IntType    = "int"
    show FloatType  = "float"
    show BoolType   = "boolean"
    show StringType = "string"
    show VoidType   = "void"
    show (VType i)  = show i
