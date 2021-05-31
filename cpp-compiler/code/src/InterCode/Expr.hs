module InterCode.Expr where

import Syntax ( Expr'(..), Field'(..), MethodCall'(..), Location'(..)
              , Identifier, fieldName
              )
import StaticCheck.TypeChecker.TypedSyntax ( TypedExpr, getTypeExpr )

import InterCode.InterCode ( InterCode, InterCode'(..), Operand(..), Label(..)
                           , Register
                           , icodeNoLabel
                           )
import InterCode.Monad ( IC, getRegister, addRegStore, isExternId )

import Control.Monad ( mapAndUnzipM )

-- Dado un registro y una expresión, retorna el código correspondiente
-- a la asignación de esa expresión en ese registro.
interCodeFromExpr :: Register -> TypedExpr -> IC InterCode
interCodeFromExpr r (Loc (LBase (FId _ i))) = 
    getRegister i >>= \rf -> return (icodeNoLabel (ICAssign (R rf) r))
interCodeFromExpr r (Loc (LBase (FIdArray _ i e))) = 
    getRegister i >>= \rf -> codeSubExpr e >>= \(op,ic) ->
    return (ic ++ icodeNoLabel (ICArrAssign rf op r))
interCodeFromExpr _ (Loc _) = error "No implementado para varias clases"
interCodeFromExpr r (Lit _ l) = return $ icodeNoLabel $ ICAssign (C l) r
interCodeFromExpr r (BOp _ op e1 e2) = 
    codeSubExpr e1 >>= \(o1,ic1) ->
    codeSubExpr e2 >>= \(o2,ic2) ->
    return (ic1 ++ ic2 ++ icodeNoLabel (BAssign op o1 o2 r))
interCodeFromExpr r (UOp _ op e) =
    codeSubExpr e >>= \(o,ic) ->
    return (ic ++ icodeNoLabel (UAssign op o r))
interCodeFromExpr r (MCall (MethodCall (LBase f) es)) = 
    interCodeFromMC (fieldName f) es >>= \ic ->
    return (ic ++ icodeNoLabel (PopReturn r))
interCodeFromExpr _ (MCall (MethodCall _ _)) = 
    error "No implementado para varias clases"
    
    
codeSubExpr :: TypedExpr -> IC (Operand,InterCode)
codeSubExpr (Lit _ l) = return (C l,[])
codeSubExpr (Loc (LBase (FId _ i))) = getRegister i >>= \r -> return (R r, [])
codeSubExpr e = addRegStore ((getTypeExpr e),1) >>= \r -> 
                interCodeFromExpr r e >>= \ic -> return (R r,ic)

interCodeFromMC :: Identifier -> [TypedExpr] -> IC InterCode
interCodeFromMC i es =
    mapAndUnzipM codeSubExpr es >>= \(ops,ics) ->
    icCall >>= \icc ->
    return ( concat ics ++ 
             icc ops
           )
    where
       icCall :: IC ([Operand] -> InterCode)
       icCall = isExternId i >>= \isExtern ->
                return $
                if isExtern
                    then icodeNoLabel . CallE (L (i,0))
                    else icodeNoLabel . Call  (L (i,0))
