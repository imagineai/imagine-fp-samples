module Syntax.PPrint.Program where

import Syntax.Program ( Program
                      , ClassDecl, ClassDecl'(..)
                      , ParamDecl(..)
                      , MethodDecl, MethodDecl'(..)
                      , Body, Body'(..)
                      )

import Syntax.PPrint.Statement ( pprintBlock, pprintFieldDecl )

import Text.PrettyPrint ( Doc, text, nest, vcat, ($$), (<+>) )

pprintProgram :: Program -> Doc
pprintProgram = vcat . map pprintClassDecl

pprintClassDecl :: ClassDecl -> Doc
pprintClassDecl (ClassDecl i fds mds) = text "ClassDecl" <+> text i
                                      $$ nest 4 (vcat (map pprintFieldDecl fds))
                                      $$ nest 4 (vcat (map pprintMethodDecl mds))

pprintMethodDecl :: MethodDecl -> Doc
pprintMethodDecl (Fun t i ps b) =  text "Fun" <+> (text $ show t)
                                <+> text i
                                <+> vcat (map pprintParamDecl ps)
                                $$ nest 4 (pprintBody b)

pprintMethodDecl (Proc i ps b) =  text "Proc"
                               <+> text i
                               <+> vcat (map pprintParamDecl ps)
                               $$ nest 4 (pprintBody b)

pprintParamDecl :: ParamDecl -> Doc
pprintParamDecl (Param t i) = text "Param" <+> text (show t) <+> text i

pprintBody :: Body -> Doc
pprintBody (Local b) = text "Local" <+> pprintBlock b
pprintBody Extern = text "Extern"
