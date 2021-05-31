module InterCode.Program where

import InterCode.Monad     ( IC, RegsAssign, getRegStore, setInitialRegMax
                           , resetRegStore, unionRegsAssign
                           , addExternId, primitiveGetRegRas
                           )
import InterCode.InterCode ( InterCode, InterCode'(..), Label
                           , icodeNoLabel, stickLabel, neutralLabel
                           , stringToLabel
                           )
import InterCode.Statement ( interCodeFromStatement
                           , interCodeFromFields
                           )

import Syntax ( Statement'(..)
              , Body'(..), FieldDecl(..)
              , Type(..), IdDecl(..)
              , ParamDecl(..), Identifier
              , ClassDecl'(..), MethodDecl'(..)
              )
import StaticCheck.TypeChecker.TypedSyntax ( TypedBody, TypedMethodDecl
                                           , TypedClassDecl
                                           )

import Control.Monad.Reader ( local )

interCodeFromClass :: TypedClassDecl -> IC InterCode
interCodeFromClass (ClassDecl _ fds mds) =
               interCodeFromFields fds >>= \(ic,ras) ->
               getRegStore >>=
               maybe (return $ icodeNoLabel $ StoreG [])
                     (\(_,tss) ->
                     setInitialRegMax (length tss) >>
                     return (icodeNoLabel $ StoreG tss)) >>= \ics ->
               resetRegStore >>
               local (unionRegsAssign ras)
                     (interCodeFromMethods mds >>= return . (++) (ics ++ ic))

interCodeFromMethods :: [TypedMethodDecl] -> IC InterCode
interCodeFromMethods []       = return []
interCodeFromMethods (md:mds) = interCodeFromMethodDecl md >>= \ic ->
                                interCodeFromMethods mds >>= \ic' ->
                                return (ic ++ ic')

interCodeFromMethodDecl :: TypedMethodDecl -> IC InterCode
interCodeFromMethodDecl (Fun ty i params body) =
                        interCodeFromMDecl ty i params body
interCodeFromMethodDecl (Proc i params body) =
                        interCodeFromMDecl VoidType i params body

interCodeFromMDecl :: Type -> Identifier -> [ParamDecl] -> TypedBody -> 
                      IC InterCode
interCodeFromMDecl _ i _ Extern = addExternId i >> return []
interCodeFromMDecl ty i params body =
           icFromBody body >>= \ic ->
           getRegStore >>=
           maybe (return $ icodeNoLabel $ Store 0 [])
                 -- Manu, el registro cero esta raro.
                 (\(r,tss) -> return $ icodeNoLabel $ Store r tss) >>= \ics ->
           resetRegStore >>
           return (stickLabel (stringToLabel i) ics ++ ic)
    where
     icFromBody :: TypedBody -> IC InterCode
     icFromBody _      = interCodeFromParams params >>= \(ic,ras) ->
                         local (unionRegsAssign ras)
                               (interCodeFromBody ty body >>=
                               return . (++) ic)
                     

interCodeFromBody :: Type -> TypedBody -> IC InterCode
interCodeFromBody _ Extern           = return []
interCodeFromBody VoidType (Local b) = interCodeFromStatement (Blck b) >>=
                                       addFinalReturn
interCodeFromBody _ (Local b)        = interCodeFromStatement $ Blck b

interCodeFromParams :: [ParamDecl] -> IC (InterCode,RegsAssign)
interCodeFromParams params = 
                    interCodeFromFields (paramsToFields params) >>= \(ic,ras) ->
                    interCodeLoadParams (reverse params) ras >>= \ic' ->
                    return (ic ++ ic', ras)

interCodeLoadParams :: [ParamDecl] -> RegsAssign -> IC InterCode
interCodeLoadParams [] _ = return []
interCodeLoadParams ps ras = return $ icodeNoLabel $ PopParams $ reverse $
                             map (flip primitiveGetRegRas ras . paramToId) ps
    where paramToId :: ParamDecl -> Identifier
          paramToId (Param _ i) = i

paramsToFields :: [ParamDecl] -> [FieldDecl]
paramsToFields = map mkField
    where mkField :: ParamDecl -> FieldDecl
          mkField (Param ty i) = FieldDecl ty [Id i]

-- Nos fijamos si la ultima instrucción es un return. Si lo es entonces
-- esta todo genial, si no lo agregamos. Esta función la usamos cuando
-- el tipo de retorno de la función es VoidType.   
addFinalReturn :: InterCode -> IC InterCode
addFinalReturn [] = return [ (neutralLabel, ICReturn) ]
addFinalReturn ic = checkLastIsReturn ic $ last ic
    where 
        checkLastIsReturn :: InterCode -> (Label,InterCode') -> IC InterCode
        checkLastIsReturn ic' (_,ICReturn) = return ic'
        checkLastIsReturn ic' _ = return $ ic' ++ [ (neutralLabel, ICReturn) ]
