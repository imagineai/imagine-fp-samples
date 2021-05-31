module StaticCheck.TypeChecker.Statement where

import Syntax ( Expr'(..), Type(..)
              , Statement, Statement'(..) , IdDecl(..)
              , FieldDecl(..), Block'(..), Identifier
              , idToLocation
              )

import StaticCheck.TypeChecker.Monad     ( TCheck, Type'(..)
                                         , terror, getLocalReturnTy, LocalCtx
                                         , addToLocalIdCtx, checkDefType
                                         )
import StaticCheck.TypeChecker.Error       ( TCError(..) )
import StaticCheck.TypeChecker.Expr        ( checkExpr, inferLoc )
import StaticCheck.TypeChecker.TypedSyntax ( TypedStatement, getTypeLoc )

import Control.Monad        ( forM, forM_, unless )
import Control.Monad.Reader ( local )
import Control.Applicative  ( (<$>) )

checkStatement :: Statement -> TCheck TypedStatement
checkStatement (Assign loc e) = inferLoc loc >>= \tyl ->
                                checkExpr e (getTypeLoc tyl) >>= 
                                return . Assign tyl
checkStatement (SMCall mc) = checkExpr (MCall mc) VoidType >>=
                             \(MCall tmc) -> return (SMCall tmc)
checkStatement (If e st mst) =
                checkExpr e BoolType >>= \tye ->
                checkStatement st >>= \tys ->
                maybe (return Nothing) ((Just <$>) . checkStatement) mst >>=
                return . If tye tys
checkStatement (For i e e' st) =
               let loc = (idToLocation i) in
               checkExpr (Loc loc) IntType >>
               checkExpr e  IntType >>= \tye ->
               checkExpr e' IntType >>= \tye' ->
               checkStatement st >>=
               return . For i tye tye'
checkStatement (While e st) =
               checkExpr e BoolType >>= \tye ->
               checkStatement st >>=
               return . While tye
checkStatement (Return me) =
               getLocalReturnTy >>= \rty ->
               maybe (unless (rty == VoidType)
                             (terror $ ReturnTypeMissMatch rty VoidType) >>
                     return (Return Nothing)
                     )
                     (\e -> checkExpr e rty >>= return . Return . Just) me

checkStatement Break    = return Break
checkStatement Continue = return Continue
checkStatement Skip     = return Skip
checkStatement (Blck (Block fds sts)) =
               checkBlockFields fds >>
               foldr (\(FieldDecl ty is) -> local (localAdd ty is))
                     (checkStatements sts) fds >>= \tyst ->
               return (Blck (Block fds tyst))
    where 
      localAdd :: Type -> [IdDecl] -> LocalCtx -> LocalCtx
      localAdd _ [] = id
      localAdd ty ((Id i):is)    = localAdd' ty is (Basic ty) i
      localAdd ty ((Arr i s):is) = localAdd' ty is (Array ty s) i
      
      localAdd' :: Type -> [IdDecl] -> Type' -> Identifier -> 
                    LocalCtx -> LocalCtx
      localAdd' ty is ty' i lctx = let lctx' = addToLocalIdCtx i ty' lctx
                                   in  localAdd ty is lctx'

checkBlockFields :: [FieldDecl] -> TCheck ()
checkBlockFields = flip forM_ checkBlockField

checkStatements :: [Statement] -> TCheck [TypedStatement]
checkStatements = flip forM checkStatement

checkBlockField :: FieldDecl -> TCheck ()
checkBlockField (FieldDecl ty is) = checkDefType ty >> checkBFs is
    where checkBFs :: [IdDecl] -> TCheck ()
          checkBFs [] = return ()
          checkBFs (i:is') = local (uncurry addToLocalIdCtx $ makeBF i)
                                   (checkBFs is')

          makeBF :: IdDecl -> (Identifier,Type')
          makeBF (Id i)    = (i, Basic ty)
          makeBF (Arr i s) = (i, Array ty s)
