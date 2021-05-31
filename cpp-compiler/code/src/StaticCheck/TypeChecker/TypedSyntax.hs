module StaticCheck.TypeChecker.TypedSyntax where

import Syntax ( Expr'(..), Location'(..), Field'(..), MethodCall'(..)
              , Statement'(..)
              , Statement', Block'(..), Body'(..), ClassDecl'(..), Program'
              , MethodDecl'(..), Type(..)
              )

type TypedExpr = Expr' Type

type TypedLoc = Location' Type

type TypedField = Field' Type

type TypedMethodCall = MethodCall' Type

type TypedStatement = Statement' Type

type TypedBlock = Block' Type

type TypedBody = Body' Type

type TypedClassDecl = ClassDecl' Type

type TypedProgram = Program' Type

type TypedMethodDecl = MethodDecl' Type

getTypeExpr :: TypedExpr -> Type
getTypeExpr (Loc loc) = getTypeLoc loc
getTypeExpr (MCall (MethodCall loc _)) = getTypeLoc loc
getTypeExpr (Lit ty _) = ty
getTypeExpr (BOp ty _ _ _) = ty
getTypeExpr (UOp ty _ _) = ty

getTypeLoc :: TypedLoc -> Type
getTypeLoc (LBase fd)  = getTypeField fd
getTypeLoc (LApp _ fd) = getTypeField fd

getTypeField :: TypedField -> Type
getTypeField (FId ty _)        = ty
getTypeField (FIdArray ty _ _) = ty
