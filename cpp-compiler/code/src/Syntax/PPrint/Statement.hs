module Syntax.PPrint.Statement where

import Syntax.Statement ( Statement, Statement'(..)
                        , Block, Block'(..)
                        , FieldDecl(..), IdDecl(..)
                        )

import Text.PrettyPrint ( Doc, integer, empty, hsep, text
                        , nest, vcat, ($$), (<+>)
                        )

pprintStatement :: Statement -> Int -> Doc
pprintStatement (Assign loc e) _ =  text "Assign" 
                                <+> text (show loc)
                                <+> text (show e)
pprintStatement (SMCall mcall) _ = text (show mcall)
pprintStatement (If e stmt mstmt) n = 
                    text "If" <+> text (show e)
                 $$ nest (n+4) (pprintStatement stmt (n+4))
                 $$ nest (n+4) (maybe empty (flip pprintStatement (n+4)) mstmt)
pprintStatement (For i e e' stmt) n = 
                    text "For" <+> text i <+> text (show e) <+> text (show e')
                 $$ nest (n+4) (pprintStatement stmt (n+4))
pprintStatement (While e stmt) n = 
                    text "While" <+> text (show e)
                 $$ nest (n+4) (pprintStatement stmt (n+4))
pprintStatement (Return me) _ = maybe (text "Return") 
                                      ((text "Return" <+>) . text . show) me
pprintStatement Break _ = text "Break"
pprintStatement Continue _ = text "Continue"
pprintStatement Skip _ = text "Skip"
pprintStatement (Blck blck) _ = pprintBlock blck

pprintBlock :: Block -> Doc
pprintBlock (Block fds stmts) = text "Block"
                             $$ vcat (map pprintFieldDecl fds)
                             $$ vcat (map (flip pprintStatement 0) stmts)

pprintFieldDecl :: FieldDecl -> Doc
pprintFieldDecl (FieldDecl t idds) =  text "FieldDecl"
                                  <+> text (show t)
                                  <+> hsep (map pprintIdDecl idds)

pprintIdDecl :: IdDecl -> Doc
pprintIdDecl (Id iden) = text "Id" <+> text iden
pprintIdDecl (Arr iden i) = text "Arr" <+> text iden <+> integer i
