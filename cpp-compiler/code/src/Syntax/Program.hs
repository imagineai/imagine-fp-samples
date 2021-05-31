{-# Language FlexibleInstances, UndecidableInstances #-}
module Syntax.Program where

import Syntax.Expr      ( Identifier, NoInfo )
import Syntax.Type      ( Type(..) )
import Syntax.Statement ( Block'(..), FieldDecl )

type Program' a = [ClassDecl' a]

type Program = Program' NoInfo

type ClassName = Identifier

data ClassDecl' a = ClassDecl ClassName [FieldDecl] [MethodDecl' a]

type ClassDecl = ClassDecl' NoInfo

data MethodDecl' a = Fun Type Identifier [ParamDecl] (Body' a)
                   | Proc Identifier [ParamDecl] (Body' a)

type MethodDecl = MethodDecl' NoInfo

data ParamDecl = Param Type Identifier

data Body' a = Local (Block' a)
             | Extern

type Body = Body' NoInfo

instance Show ClassDecl where
    show (ClassDecl c fds mds) = "class " ++ c ++ 
                                 unlines [ show fds
                                         , show mds ]

instance Show MethodDecl where
    show (Fun ty i ps b) = unwords [ show ty
                                   , i
                                   , show ps
                                   , "{\n" ++ show b ++ "\n}\n"
                                   ]
    show (Proc i ps b) = unwords [ show VoidType
                                 , i
                                 , show ps
                                 , "{\n" ++ show b ++ "\n}\n"
                                 ]
        

instance Show ParamDecl where
    show (Param ty i) = unwords [ show ty
                                , i
                                ]
                                
instance Show Body where
    show (Local b) = show b
    show Extern    = "extern"
