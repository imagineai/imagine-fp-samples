{- Expresiones del lenguaje While de acuerdo al libro 
   "Computability and Complexity" de Neil Jones. -}

module Expr ( Expr (..)
            , exprvars
            , pprintExpr
            , valAsExpr
            ) where

import Value

import Text.PrettyPrint

data Expr = V Var
          | A Atom
          | Cons Expr Expr
          | Hd Expr
          | Tl Expr
          | Eq Expr Expr
          | Star
          | Univ Expr Expr
    deriving (Show,Eq)

pprintExpr :: Expr -> Doc
pprintExpr (V v)        = int v
pprintExpr (Cons e1 e2) = text "cons" <+> pprintExpr e1 <+> pprintExpr e2
pprintExpr (Hd e)       = text "hd"   <+> pprintExpr e
pprintExpr (Tl e)       = text "tl"   <+> pprintExpr e
pprintExpr (Eq e1 e2)   = text "=?"   <+> pprintExpr e1 <+> pprintExpr e2
pprintExpr (Univ e1 e2) = text "univ" <+> pprintExpr e1 <+> pprintExpr e2
pprintExpr Star         = text "*"
pprintExpr (A _)        = text "nil"

exprvars :: Expr -> [Var]
exprvars (V v)        = [v]
exprvars (Cons e1 e2) = exprvars e1 ++ exprvars e2
exprvars (Hd e)       = exprvars e
exprvars (Tl e)       = exprvars e
exprvars (Eq e1 e2)   = exprvars e1 ++ exprvars e2
exprvars (Univ e1 e2) = exprvars e1 ++ exprvars e2
exprvars _            = []

-- Comentar bien esto!
valAsExpr :: Value -> Expr
valAsExpr (VAtom a)   = A a
valAsExpr (Dot v v') = Cons (valAsExpr v) (valAsExpr v')
