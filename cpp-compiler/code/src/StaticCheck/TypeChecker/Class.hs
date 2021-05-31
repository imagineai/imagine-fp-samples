module StaticCheck.TypeChecker.Class where

import Syntax ( Type(..)
              , ClassDecl, ClassDecl'(..)
              , Statement'(..)
              , MethodDecl, MethodDecl'(..)
              , Body, Body'(..)
              , FieldDecl(..), ParamDecl(..), Identifier
              , ideclToId
              )

import StaticCheck.TypeChecker.Monad ( TCheck, Type'(..)
                                     , terror, mkType'
                                     , addToLocalRTyCtx
                                     , addToLocalIdCtx
                                     , addIdToClassCtx
                                     , addClassName, getCNames
                                     , addToLocalClassName
                                     , addMthdToClassCtx
                                     , whenIsLocalDef, whenMethodIsDef
                                     , checkDefType, whenIsGlobalDef
                                     , getLocalCname
                                     )
import StaticCheck.TypeChecker.Error       ( TCError(..) )    
import StaticCheck.TypeChecker.Statement   ( checkStatement )
import StaticCheck.TypeChecker.TypedSyntax ( TypedClassDecl, TypedMethodDecl
                                           , TypedBody
                                           )

import Control.Monad.RWS ( forM, forM_, local )

checkClass :: ClassDecl -> TCheck TypedClassDecl
checkClass (ClassDecl c fdecls mdecls) =
    checkClassName c >>
    local (addToLocalClassName c) 
          (checkClassFields fdecls >>
           checkMethodDecls mdecls) >>= \tymthds ->
    return (ClassDecl c fdecls tymthds)
    
-- Chequea que el identificador no esté definido como clase
-- y lo agrega 
checkClassName :: Identifier -> TCheck ()
checkClassName v =
    getCNames >>= \cns ->
    if elem v cns 
       then terror $ RedefClass v
       else addClassName v

checkClassFields :: [FieldDecl] -> TCheck ()
checkClassFields fds = forM_ fds checkClassField

checkClassField :: FieldDecl -> TCheck ()
checkClassField (FieldDecl ty is) =
    checkDefType ty >> forM_ is addId
    where addId idecl =
            let ty' = mkType' idecl ty
                i   = ideclToId idecl in
                getLocalCname >>= \cn ->
                whenIsGlobalDef cn i (terror $ RedefId cn i) >>
                addIdToClassCtx cn i ty'
               
checkMethodDecls :: [MethodDecl] -> TCheck [TypedMethodDecl]
checkMethodDecls mds = forM mds checkMethodDecl

checkMethodDecl :: MethodDecl -> TCheck TypedMethodDecl
checkMethodDecl (Fun ty i params body) = 
                checkMethodName i ty params >>
                foldr (\(Param t i') -> local (addToLocalIdCtx i' (Basic t)))
                      (checkBody ty body) params >>= \tybody ->
                return (Fun ty i params tybody)
checkMethodDecl (Proc i params body) = 
                checkMethodName i VoidType params >> 
                foldr (\(Param t i') -> local (addToLocalIdCtx i' (Basic t)))
                      (checkBody VoidType body) params >>= \tybody ->
                return (Proc i params tybody)
    
checkMethodName :: Identifier -> Type -> [ParamDecl] -> 
                   TCheck ()
checkMethodName i rTy params =
        getLocalCname >>= \cn ->
        -- chequeamos que el nombre del metodo no este definido como variable
        whenIsGlobalDef cn i (terror $ RedefId cn i) >>
        -- chequeamos que el nombre del método no esté definido como métdodo
        whenMethodIsDef cn i (terror $ RedefId cn i) >>
        -- checkParams chequea que no haya doble definicion en los parametros y
        -- agrega las variables al contexto local
        checkParams params >>
        addMthdToClassCtx cn i rTy (map (\(Param t _) -> t) params) 

    where checkParams :: [ParamDecl] -> TCheck ()
          checkParams []     = return ()
          checkParams (p:ps) = checkParam p >>= \(i',t) ->
                               local (addToLocalIdCtx i' t) (checkParams ps)
          checkParam :: ParamDecl -> TCheck (Identifier,Type')
          checkParam (Param ty i') =
              checkDefType ty >>
              -- chequeamos doble definicion de parametros
              whenIsLocalDef i' (terror $ RedefParam i') >>
              return (i',Basic ty)

checkBody :: Type -> Body -> TCheck TypedBody
checkBody _ Extern = return Extern
checkBody rTy (Local b) = local (addToLocalRTyCtx rTy) 
                                (checkStatement (Blck b)) >>= \(Blck tyb) ->
                                return (Local tyb)
