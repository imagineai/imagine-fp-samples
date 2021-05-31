module StaticCheck.TypeChecker.PPrint where

import Syntax ( Expr'(..), Location'(..), Field'(..), MethodCall'(..)
              , Statement'(..), FieldDecl(..), IdDecl(..), ParamDecl(..)
              , Block'(..), Body'(..), ClassDecl'(..), MethodDecl'(..), Type(..)
              )

import StaticCheck.TypeChecker.TypedSyntax

import Text.PrettyPrint ( Doc, integer, empty, hsep, text, comma, colon
                        , nest, vcat, ($$), (<+>), parens, brackets
                        )

pprintTyExpr :: TypedExpr -> Doc
pprintTyExpr (Loc l)    = pprintTyLoc l
pprintTyExpr (MCall mc) = pprintTyMC mc
pprintTyExpr (Lit t l)  = parens $ text (show l) <+> colon <+> text (show t)
pprintTyExpr (BOp t bop e1 e2) = printType (parens (pprintTyExpr e1)
                                           <+> text (show bop)
                                           <+> parens (pprintTyExpr e2)
                                           ) t
pprintTyExpr (UOp t uop e)     = printType 
                                 (text (show uop) <+> parens (pprintTyExpr e)) t

pprintTyLoc :: TypedLoc -> Doc
pprintTyLoc (LBase f) = pprintTyField f
pprintTyLoc  (LApp l f) = pprintTyLoc l <+> text "." <+> pprintTyField f

pprintTyField :: TypedField -> Doc
pprintTyField (FId t i) = printType (text i) t
pprintTyField (FIdArray t i e) = printType 
                                 (text i <+> brackets (pprintTyExpr e)) t

pprintTyMC :: TypedMethodCall -> Doc
pprintTyMC (MethodCall l es) = pprintTyLoc l <+> parens (printEs es)
    where printEs :: [TypedExpr] -> Doc
          printEs []        = empty
          printEs (e:[])    = pprintTyExpr e
          printEs (e:_:es') = pprintTyExpr e <+> comma <+> printEs es'

pprintTyMD :: TypedMethodDecl -> String
pprintTyMD (Fun ty i ps b) = unwords [ show ty
                                     , i
                                     , show ps
                                     , "{\n" ++ show (pprintTyBody b) ++ "\n}\n"
                                     ]
pprintTyMD (Proc i ps b) = unwords [ show VoidType
                                   , i
                                   , show ps
                                   , "{\n" ++ show (pprintTyBody b) ++ "\n}\n"
                                   ]

printType :: Doc -> Type -> Doc
printType s t = parens s <+> text ":" <+> text (show t)

pprintTyStatement :: TypedStatement -> Int -> Doc
pprintTyStatement (Assign loc e) _ =  text "Assign" 
                                  <+> pprintTyLoc loc
                                  <+> pprintTyExpr e
pprintTyStatement (SMCall mcall) _ = pprintTyMC mcall
pprintTyStatement (If e stmt mstmt) n = 
                    text "If" <+> pprintTyExpr e
                 $$ nest (n+4) (pprintTyStatement stmt (n+4))
                 $$ nest (n+4) (maybe empty (flip pprintTyStatement (n+4)) mstmt)
pprintTyStatement (For i e e' stmt) n =
                    text "For" <+> text i <+> pprintTyExpr e
                                          <+> pprintTyExpr e'
                 $$ nest (n+4) (pprintTyStatement stmt (n+4))
pprintTyStatement (While e stmt) n = 
                    text "While" <+> pprintTyExpr e
                 $$ nest (n+4) (pprintTyStatement stmt (n+4))
pprintTyStatement (Return me) _ = maybe 
                                  (text "Return") 
                                  ((text "Return" <+>) . pprintTyExpr) me
pprintTyStatement Break _ = text "Break"
pprintTyStatement Continue _ = text "Continue"
pprintTyStatement Skip _ = text "Skip"
pprintTyStatement (Blck blck) _ = pprintTyBlock blck

pprintTyBlock :: TypedBlock -> Doc
pprintTyBlock (Block fds stmts) = text "Block"
                             $$ vcat (map pprintFieldDecl fds)
                             $$ vcat (map (flip pprintTyStatement 0) stmts)

pprintFieldDecl :: FieldDecl -> Doc
pprintFieldDecl (FieldDecl t idds) =  text "FieldDecl"
                                  <+> text (show t)
                                  <+> hsep (map pprintIdDecl idds)

pprintIdDecl :: IdDecl -> Doc
pprintIdDecl (Id iden) = text "Id" <+> text iden
pprintIdDecl (Arr iden i) = text "Arr" <+> text iden <+> integer i

pprintTyProgram :: TypedProgram -> Doc
pprintTyProgram = vcat . map pprintTyClassDecl

pprintTyClassDecl :: TypedClassDecl -> Doc
pprintTyClassDecl (ClassDecl i fds mds) = text "ClassDecl" <+> text i
                                   $$ nest 4 (vcat (map pprintFieldDecl fds))
                                   $$ nest 4 (vcat (map pprintTyMethodDecl mds))

pprintTyMethodDecl :: TypedMethodDecl -> Doc
pprintTyMethodDecl (Fun t i ps b) =  text "Fun" <+> (text $ show t)
                                <+> text i
                                <+> vcat (map pprintParamDecl ps)
                                $$ nest 4 (pprintTyBody b)
pprintTyMethodDecl (Proc i ps b) =  text "Proc"
                               <+> text i
                               <+> vcat (map pprintParamDecl ps)
                               $$ nest 4 (pprintTyBody b)

pprintParamDecl :: ParamDecl -> Doc
pprintParamDecl (Param t i) = text "Param" <+> text (show t) <+> text i

pprintTyBody :: TypedBody -> Doc
pprintTyBody (Local b) = text "Local" <+> pprintTyBlock b
pprintTyBody Extern = text "Extern"
