module InterCode.Statement where

import InterCode.Expr      ( interCodeFromExpr, interCodeFromMC )
import InterCode.Monad     ( IC, RegsAssign, addRegsAssign, addRegStore
                           , askRegsAssign, updateRegsAssign
                           , askContinueLabel, askBreakLabel, getRegister
                           , addContinueLabel, addBreakLabel
                           , getLabelMaxWithString
                           , unionRegsAssign, updateLabelMax
                           )
import InterCode.InterCode ( InterCode, InterCode'(..), Register, Operand(..)
                           , neutralLabel, icodeNoLabel, stickLabel
                           )

import StaticCheck.TypeChecker ( TypedExpr, TypedField, TypedBlock
                               , TypedStatement, getTypeExpr
                               )

import Syntax ( Expr'(..), Location'(..), Statement'(..)
              , MethodCall'(..), Block'(..)
              , Field'(..), RelOp(..)
              , FieldDecl(..)
              , Type(..), IdDecl(..)
              , Identifier
              , BinOp(..), ArithOp(..), Literal(..)
              , fieldName, idToLocation'
              )

import Control.Arrow     ( (***) )
import Control.Monad.RWS ( local )

interCodeFromStatement :: TypedStatement -> IC InterCode
interCodeFromStatement (Assign (LBase f) e) = interCodeFromAssign f e
interCodeFromStatement (Assign _ _)       = error "No implementado"
interCodeFromStatement (SMCall (MethodCall (LBase f) es)) =
                                              interCodeFromMC (fieldName f) es
interCodeFromStatement (If e stmt mstmt)    = interCodeFromIFStmt e stmt mstmt
interCodeFromStatement (For i e e' stmt)    = interCodeFromForStmt i e e' stmt
interCodeFromStatement (While e stmt)       = interCodeFromWhileStmt e stmt
interCodeFromStatement (Return me)          = interCodeFromReturnStmt me
interCodeFromStatement Break                = interCodeFromBreak
interCodeFromStatement Continue             = interCodeFromContinue
interCodeFromStatement Skip                 = return []
interCodeFromStatement (Blck blck)          = interCodeFromBlock blck
interCodeFromStatement _                    = error "No implementado"

interCodeFromStatements :: [TypedStatement] -> IC InterCode
interCodeFromStatements []       = return []
interCodeFromStatements (stmt:mds) = interCodeFromStatement stmt >>= \ic ->
                                     interCodeFromStatements mds >>= \ic' ->
                                     return (ic ++ ic')

interCodeFromBlock :: TypedBlock -> IC InterCode
interCodeFromBlock (Block fds stmts) = 
                   interCodeFromFields fds >>= \(ic,ras) ->
                   local (unionRegsAssign ras)
                         (interCodeFromStatements stmts >>= return . (++) ic)

interCodeFromAssign :: TypedField -> TypedExpr -> IC InterCode
interCodeFromAssign (FId _ i) e = 
                    getRegister i >>= \r ->
                    interCodeFromExpr r e >>= return
interCodeFromAssign (FIdArray _ i e') e =
                    getRegister i >>= \r ->
                    addRegStore ((getTypeExpr e),1) >>= \re ->
                    addRegStore ((getTypeExpr e'),1) >>= \re' ->
                    interCodeFromExpr re e >>= \ice ->
                    interCodeFromExpr re' e' >>= \ics ->
                    let ic' = [(neutralLabel ,AssignArray (R re) (R re') r)]
                    in return (ics ++ ice ++ ic')

interCodeFromIFStmt :: TypedExpr -> TypedStatement -> (Maybe TypedStatement) ->
                       IC InterCode
interCodeFromIFStmt e stmt (Just stmt') = 
                    addRegStore ((getTypeExpr e),1) >>= \re ->
                    interCodeFromExpr re e >>= \ic ->
                    getLabelMaxWithString "TRUE" >>= \ltrue ->
                    getLabelMaxWithString "FALSE" >>= \lfalse ->
                    getLabelMaxWithString "END" >>= \lend ->
                    updateLabelMax >>
                    interCodeFromStatement stmt >>= \stmtic ->
                    interCodeFromStatement stmt' >>= \stmtic' ->
                    return ( ic
                          ++ [ (neutralLabel, JumpCnd (R re) ltrue lfalse) ]
                          ++   stickLabel ltrue stmtic
                          ++ [ (neutralLabel, Jump lend) ]
                          ++   stickLabel lfalse stmtic'
                          ++ [ (lend,ICSkip) ]
                           )
interCodeFromIFStmt e stmt Nothing = 
                      addRegStore ((getTypeExpr e),1) >>= \re ->
                      interCodeFromExpr re e >>= \ic ->
                      getLabelMaxWithString "TRUE" >>= \ltrue ->
                      getLabelMaxWithString "END" >>= \lend ->
                      updateLabelMax >>
                      interCodeFromStatement stmt >>= \stmtic ->
                      return ( ic
                            ++ [ (neutralLabel, JumpCnd (R re) ltrue lend) ]
                            ++   stickLabel ltrue stmtic
                            ++ [ (neutralLabel, Jump lend) ]
                            ++ [ (lend,ICSkip) ]
                             )

interCodeFromForStmt :: Identifier -> TypedExpr -> TypedExpr ->
                        TypedStatement -> IC InterCode
interCodeFromForStmt i e e' stmt =
                  interCodeFromAssign (FId IntType i) e >>= \ic ->
                  addRegStore (BoolType,1) >>= \rcond ->
                  interCodeFromExpr rcond cond >>= \ic' ->
                  getLabelMaxWithString "FORTRUE" >>= \ltrue ->
                  getLabelMaxWithString "FORFALSE" >>= \lfalse ->
                  getLabelMaxWithString "FORSTART" >>= \lstart ->
                  updateLabelMax >>
                  local (addContinueLabel ltrue . addBreakLabel lfalse)
                        (interCodeFromStatement stmt) >>= \icstmt ->
                  getRegister i >>= \regi ->
                  return (   ic
                        ++   stickLabel lstart ic'
                        ++ [ (neutralLabel, JumpCnd (R rcond) ltrue lfalse) ]
                        ++   stickLabel ltrue icstmt
                        ++ plusone regi
                        ++ [ (neutralLabel, Jump lstart) ]
                        ++ [ (lfalse,ICSkip) ]
                         )
    where
        cond :: TypedExpr
        cond = BOp BoolType (Rel Leq) (Loc $ idToLocation' IntType i) e'
        plusone :: Register -> InterCode
        plusone r = [(neutralLabel,BAssign (Arith Plus) (R r) (C (IntL 1)) r)]

interCodeFromWhileStmt :: TypedExpr -> TypedStatement -> IC InterCode
interCodeFromWhileStmt e stmt = 
                    addRegStore ((getTypeExpr e),1) >>= \re ->
                    interCodeFromExpr re e >>= \ic ->
                    getLabelMaxWithString "WHILETRUE" >>= \ltrue ->
                    getLabelMaxWithString "WHILEFALSE" >>= \lfalse ->
                    getLabelMaxWithString "WHILESTART" >>= \lstart ->
                    updateLabelMax >>
                    local (addContinueLabel ltrue . addBreakLabel lfalse)
                          (interCodeFromStatement stmt) >>= \icstmt ->
                    return (   stickLabel lstart ic
                          ++ [ (neutralLabel, JumpCnd (R re) ltrue lfalse) ]
                          ++   stickLabel ltrue icstmt
                          ++ [ (neutralLabel, Jump lstart) ]
                          ++ [ (lfalse,ICSkip) ]
                           )

interCodeFromReturnStmt :: Maybe TypedExpr -> IC InterCode
interCodeFromReturnStmt Nothing  = return [ (neutralLabel, ICReturn) ]
interCodeFromReturnStmt (Just e) = 
          addRegStore ((getTypeExpr e),1) >>= \re ->
          interCodeFromExpr re e >>= \ic ->
          let ic' = icodeNoLabel (PutReturn re)
          in return (ic ++ ic' ++ [ (neutralLabel, ICReturn) ])

interCodeFromBreak :: IC InterCode
interCodeFromBreak = askBreakLabel >>= \lbreak ->
                     return [ (neutralLabel, Jump lbreak) ]

interCodeFromContinue :: IC InterCode
interCodeFromContinue = askContinueLabel >>= \lcont ->
                        return [ (neutralLabel, Jump lcont) ]
                        
interCodeFromFields :: [FieldDecl] -> IC (InterCode,RegsAssign)
interCodeFromFields [] = askRegsAssign >>= \ras -> return ([], ras)
interCodeFromFields (fs:fds) = interCodeFromField fs >>= \(ic,ras) ->
                               local (updateRegsAssign ras)
                                     (interCodeFromFields fds) >>=
                               return . (***) ((++) ic) id

interCodeFromField :: FieldDecl -> IC (InterCode,RegsAssign)
interCodeFromField (FieldDecl ty ids) = interCodeFromIdDecls ty ids

interCodeFromIdDecls :: Type -> [IdDecl] -> IC (InterCode,RegsAssign)
interCodeFromIdDecls _ [] = askRegsAssign >>= \ras -> return ([], ras)
interCodeFromIdDecls ty ((Id i):ids) = icFromIdDecl ty i 1 ids
interCodeFromIdDecls ty ((Arr i size):ids) = icFromIdDecl ty i size ids

icFromIdDecl :: Type -> Identifier -> Integer -> [IdDecl] ->
                IC (InterCode,RegsAssign)
icFromIdDecl ty i s ids = addRegStore (ty,s) >>= \r ->
                          local (addRegsAssign i r)
                                (interCodeFromIdDecls ty ids) >>= \(ic,ras) ->
                          return (ic,ras)
