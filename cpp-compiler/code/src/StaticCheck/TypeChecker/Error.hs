module StaticCheck.TypeChecker.Error where

import Syntax ( ClassName, Type, Identifier )
import StaticCheck.TypeChecker.TypedSyntax ( TypedExpr )
import StaticCheck.TypeChecker.PPrint ( pprintTyExpr )

data TCError = RedefClass Identifier
             | NotDefClass Identifier
             | RedefId    ClassName Identifier
             | RedefParam Identifier
             | NotDef     Identifier
             | AttrNotDef ClassName Identifier
             | MthdNotDef ClassName Identifier
             | NArgsNotValid ClassName Identifier
             | VarIsArray Identifier
             | VarIsId    Identifier
             | TypeMissMatch TypedExpr Type Type
             | TypeNotClass Type
             | ReturnTypeMissMatch Type Type

instance Show TCError where
    show (RedefClass c)   = "Clase " ++ c ++ " redefinida."
    show (NotDefClass c)  = "Clase " ++ c ++ " no definida."
    show (RedefId c i)      = "Variable " ++ i ++ " redefinida en la clase "
                             ++ c
    show (RedefParam p)   = "Parámetro " ++ p ++ " redefinida."
    show (NotDef i)       = "Variable " ++ show i ++ " no definida."
    show (AttrNotDef c i) = "Atributo " ++ i ++ " de la clase " ++ c ++ " no definido."
    show (MthdNotDef c i) = "Método " ++ i ++ " de la clase " ++ c ++ " no definido."
    show (NArgsNotValid c i) = "La cantidad de argumentos del método " ++ i ++ " de la clase " ++ c ++
                                " no es correcta."
    show (VarIsArray i)     = "La variable " ++ i ++ " está definida como array."
    show (VarIsId i)        = "La variable " ++ i ++ " no está definida como array."
    show (TypeMissMatch e t1 t2) = "El tipo \"" ++ show t1 ++ "\" no coincide con el tipo \"" ++
                                    show t2 ++ "\" en la expresión " ++ show (pprintTyExpr e)
    show (TypeNotClass t) = "El tipo " ++ show t ++ " no corresponde a una clase."
    show (ReturnTypeMissMatch t1 t2) = "El método tiene como tipo de retorno " ++ show t1 ++
                                       " y no " ++ show t2
