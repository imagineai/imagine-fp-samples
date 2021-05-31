{- Al lenguaje base se le agregan construcciones
como syntactic sugar. Este módulo define el lenguaje intermedio
que luego se traduce al base. -}

module ExtendedLanguage.ExtLanguage ( Pattern (..)
                                    , Rule (..)
                                    , ExtComm (..)
                                    , Name
                                    , ProgNames
                                    , ExtProg (..)
                                    , etrue
                                    , efalse
                                    , skip
                                    , valAsPatt
                                    ) where

import Expr
import Value

import qualified Data.Map as M

data Pattern = PVar Var
             | PNil
             | PDot Pattern Pattern
    deriving Show

data Rule = RuleE [(Pattern,Expr)]
          | RuleC [Pattern] ExtComm
    deriving Show

data ExtComm = EAssgn Var Expr
             | ESeq ExtComm ExtComm
             | EWhile Expr ExtComm
             | If Expr ExtComm
             | IfElse Expr ExtComm ExtComm
             | Rewrite [Var] [Rule]
             | Case Var [(Pattern,ExtComm)]
             | Call Var Name Var
    deriving Show

-- Nombre de un programa
type Name = String
    
data ExtProg = ExtProg { xread  :: Var
                       , xcomm  :: ExtComm
                       , xwrite :: Var
                       -- Maxima variable de este programa
                       , maxvar :: Var
               } 
               
--Mapa de nombres de programas
type ProgNames = M.Map Name ExtProg
             
{- Booleanos -}

-- True
etrue :: Expr
etrue = Cons (A Nil) (A Nil)

-- False
efalse :: Expr
efalse = A Nil

skip :: ExtComm
skip = EAssgn oneVar (V oneVar)

valAsPatt :: Value -> Pattern
valAsPatt (VAtom _) = PNil
valAsPatt (Dot v v') = PDot (valAsPatt v) (valAsPatt v')
