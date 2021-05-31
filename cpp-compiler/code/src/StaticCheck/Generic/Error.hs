module StaticCheck.Generic.Error where

import Syntax ( Identifier )

type GenericErrors = [GenericError]

data GenericError = MissingMethodMain
                  | IncorrectPrototipeMain
                  | IncorrectArraySize [Identifier]
                  | MisplacedBreak     [Identifier]
                  | MisplacedContinue  [Identifier]
                  | MissingReturn      [Identifier]

instance Show GenericError where
    show MissingMethodMain       = "No se encuentra el método main."
    show IncorrectPrototipeMain  =
      "El método main no tiene el prototipo adecuado."
    show (IncorrectArraySize is) =
      "Arrays con tamaño incorrecto: " ++ show is
    show (MisplacedBreak is)     =
      "Sentencia Break inválida en los métodos: " ++ show is
    show (MisplacedContinue is)  =
      "Sentencia Continue inválida en los métodos: " ++ show is
    show (MissingReturn is)      =
      "Falta la instrucción return en los métodos: " ++ show is
