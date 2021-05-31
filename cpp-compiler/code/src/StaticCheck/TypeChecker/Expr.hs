module StaticCheck.TypeChecker.Expr where

import Syntax ( Expr, Expr'(..), Type(..), BinOp(..)
              , Literal(..), MethodCall, MethodCall'(..)
              , Location, Location'(..), Identifier
              , ClassName, Field, Field'(..)
              , isNum, locIdName, subtype
              )
import StaticCheck.TypeChecker.Monad     ( TCheck, Type'(..)
                                         , terror, getTypeFromMthdCtx
                                         , checkIsDefClass, getLocalCname
                                         , getMthdType, unlessMethodIsDef
                                         , unlessIsGlobalDef, getIdType
                                         , unlessIsLocalDef, addToLocalClassName
                                         )
import StaticCheck.TypeChecker.Error       ( TCError(..) )
import StaticCheck.TypeChecker.TypedSyntax ( TypedExpr, TypedMethodCall
                                           , TypedLoc, TypedField
                                           , getTypeExpr, getTypeLoc
                                           )

import Control.Arrow ( (***) )
import Control.Monad (unless,zipWithM)
import Control.Monad.Reader (local)       

-- chequea si dos tipos son iguales
checkConversion :: TypedExpr -> Type -> TCheck ()
checkConversion tye ty = 
    unless (getTypeExpr tye == ty)
           (terror $ TypeMissMatch tye (getTypeExpr tye) ty)

-- Esta función chequea solamente en el contexto global.
inferFieldGlobal :: Field -> TCheck TypedField
inferFieldGlobal = inferField' 
                   (\i cn -> 
                   unlessIsGlobalDef cn i (terror $ NotDef i))

-- Esta función chequea en el contexto global y local.
inferField :: Field -> TCheck TypedField
inferField  = inferField' 
              (\i cn ->
              unlessIsLocalDef i
              (unlessIsGlobalDef cn i (terror $ NotDef i)))

inferField' :: (Identifier -> ClassName -> TCheck ()) -> Field ->
              TCheck TypedField
inferField' fty f@(FId _ i) = 
    getLocalCname >>= \cn ->
    fty i cn >> getIdType i >>= 
    checkId f >>= \ty -> return (FId ty i)
inferField' fty f@(FIdArray _ i e) =
    getLocalCname >>= \cn ->
    fty i cn >> getIdType i >>= 
    checkId f >>= \ty ->
    inferExpr e >>= \tye ->
    checkConversion tye IntType >>
    return (FIdArray ty i tye)

checkId :: Field -> Type' -> TCheck Type
checkId (FId _ i) t' = 
    case t' of
        Basic ty  -> return ty
        Array _ _ -> terror (VarIsArray i)
checkId (FIdArray _ i _) t' =
    case t' of
        Basic _   -> terror (VarIsId i)
        Array ty _ -> return ty

inferLoc :: Location -> TCheck TypedLoc
inferLoc (LBase f)    = inferField f >>= return . LBase
inferLoc (LApp loc f) = inferLoc loc >>= \tyl ->
                        checkIsDefClass (getTypeLoc tyl) >>= \(VType c) ->
                        local (addToLocalClassName c) (inferFieldGlobal f) >>=
                        return . LApp tyl

inferFieldMthd :: Field -> TCheck (TypedField,[Type])
inferFieldMthd (FId _ i) = getLocalCname >>= \cn ->
                           unlessMethodIsDef cn i (terror $ MthdNotDef cn i) >>
                           getMthdType i >>= return . (flip FId i *** id)
inferFieldMthd (FIdArray _ _ _) =
    error "inferFieldMthd: IMPOSIBLE: Un nombre de método no puede ser un array."

inferLocMthd :: Location -> TCheck (ClassName,TypedLoc,[Type])
inferLocMthd (LBase f)    = 
    getLocalCname >>= \cn ->
    inferFieldMthd f >>= \(tyf,tys) ->
    return (cn,LBase tyf,tys)
inferLocMthd (LApp loc (FId _ i)) =
    inferLoc loc >>= \tyl ->
    checkIsDefClass (getTypeLoc tyl) >>= \(VType c) ->
    getTypeFromMthdCtx c i >>=
    maybe (terror $ MthdNotDef c i) 
          (\(rty,tys) -> return (c,LApp tyl (FId rty i),tys))
inferLocMthd _ = error "inferLocMthd: IMPOSIBLE"
        
inferMCall :: MethodCall -> TCheck TypedMethodCall
inferMCall (MethodCall loc args) =
    inferLocMthd loc >>= \(cn,tyl,tys) ->
    unless (length args == length tys)
           (terror $ NArgsNotValid cn $ locIdName loc) >>
    zipWithM checkExpr args tys >>= return . MethodCall tyl
    
    
inferLiteral :: Literal -> TCheck Type
inferLiteral (IntL _)   = return IntType
inferLiteral (FloatL _) = return FloatType
inferLiteral (BoolL _)  = return BoolType
inferLiteral (StringL _) = return StringType

inferBinOp :: BinOp -> Expr -> Expr -> TCheck TypedExpr
inferBinOp op@(Arith _) e1 e2 =
    inferExpr e1 >>= \tye1 -> inferExpr e2 >>= \tye2 ->
    let t1 = getTypeExpr tye1
        t2 = getTypeExpr tye2
        mty = subtype t1 t2
    in unless (isNum t1) (terror $ TypeMissMatch tye1 t1 FloatType) >>
       unless (isNum t2) (terror $ TypeMissMatch tye2 t2 FloatType) >>
       maybe (error "inferBinOp: imposible") 
             (\ty -> return (BOp ty op tye1 tye2)) mty
inferBinOp op@(Cond _) e1 e2 = 
    inferExpr e1 >>= \tye1 -> inferExpr e2 >>= \tye2 ->
    checkConversion tye1 BoolType >>
    checkConversion tye2 BoolType >>
    return (BOp BoolType op tye1 tye2)
inferBinOp op@(Rel _) e1 e2 = 
    inferExpr e1 >>= \tye1 -> inferExpr e2 >>= \tye2 ->
    let t1 = getTypeExpr tye1
        t2 = getTypeExpr tye2
    in unless (isNum t1) (terror $ TypeMissMatch tye1 t1 FloatType) >>
       unless (isNum t2) (terror $ TypeMissMatch tye2 t2 FloatType) >>
       return (BOp BoolType op tye1 tye2)
inferBinOp op@(Eq _) e1 e2 =
    inferExpr e1 >>= \tye1 -> inferExpr e2 >>= \tye2 ->
    let t1 = getTypeExpr tye1
        t2 = getTypeExpr tye2
    in unless (t1 == t2) (terror $ TypeMissMatch tye1 t1 t2) >>
       return (BOp BoolType op tye1 tye2)

inferExpr :: Expr -> TCheck TypedExpr
inferExpr (Loc loc)       = inferLoc loc >>= return . Loc
inferExpr (MCall mc)      = inferMCall mc >>= return . MCall
inferExpr (Lit _ lit)       = inferLiteral lit >>=
                              return . flip Lit lit
inferExpr (BOp _ bop e1 e2) = inferBinOp bop e1 e2
inferExpr (UOp _ uop e)     = inferExpr e >>= \tye ->
                              checkConversion tye BoolType >> 
                              return (UOp BoolType uop tye)
    
checkExpr :: Expr -> Type -> TCheck TypedExpr
checkExpr e t = inferExpr e >>= \tye ->
                checkConversion tye t >>
                return tye
