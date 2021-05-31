{-# Language FlexibleInstances, UndecidableInstances #-}
module Syntax.Statement where

import Syntax.Expr
import Syntax.Type

data Statement' a = Assign (Location' a) (Expr' a)
                  | SMCall (MethodCall' a)
                  | If (Expr' a) (Statement' a) (Maybe (Statement' a))
                  | For Identifier (Expr' a) (Expr' a) (Statement' a)
                  | While (Expr' a) (Statement' a)
                  | Return (Maybe (Expr' a))
                  | Break
                  | Continue
                  | Skip
                  | Blck (Block' a)

type Statement = Statement' NoInfo

data Block' a = Block [FieldDecl] [Statement' a]

type Block = Block' NoInfo

data FieldDecl = FieldDecl Type [IdDecl]
     deriving Show

data IdDecl = Id Identifier | Arr Identifier Integer
     deriving Show
     
ideclToId :: IdDecl -> Identifier
ideclToId (Id i)    = i
ideclToId (Arr i _) = i

instance Show Statement where
    show (Assign l e) = show l ++ " = " ++ show e
    show (SMCall mc)  = show mc
    show (If e st mst) = "if " ++ "(" ++ show e ++ ") " ++ show st ++ showmst
        where showmst = maybe "" (\st' -> " else " ++ show st') mst
    show (For i e1 e2 st) = "for " ++ i ++ " = " ++ show e1 ++ ", " ++ show e2 ++
                             show st
    show (While e st) = "while " ++ show e ++ " " ++ show st
    show (Return me)  = "return" ++ maybe "" (\e -> " " ++ show e) me
    show Break        = "break"
    show Continue     = "continue"
    show Skip         = "skip"
    show (Blck bl)    = show bl

instance Show Block where
    show (Block fds sts) = "{ " ++ show fds ++ "\n" ++ show sts ++ " } "
