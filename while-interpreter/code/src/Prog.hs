{- Programas del lenguaje While de acuerdo al libro 
   "Computability and Complexity" de Neil Jones. -}

module Prog ( Comm(..)
            , Prog(..)
            , (<.>)
            , vars
            , nextFreeVar
            ) where

import Expr
import Value

import Prelude hiding ( read )
import Data.List ( nub )
import Text.PrettyPrint

data Comm = Assgn Var Expr
          | Seq Comm Comm
          | While Expr Comm 
    deriving Eq

instance Show Comm where
    show = show . flip pprintComm 0

pprintProg :: Prog -> Doc
pprintProg p = (text "read" <+> text (show $ read p)) $$
               nest 4 (pprintComm (prg p) 0) $$
               (text "write" <+> text (show $ write p))

pprintComm :: Comm -> Int ->Doc
pprintComm (Assgn v e) _ = int v <+> text ":=" <+> pprintExpr e
pprintComm (Seq c c')  n = (pprintComm c n <> text ";") $$ pprintComm c' n
pprintComm (While e c) n = (text "while" <+> pprintExpr e <+> text "do") $$
                           nest (n+4) (pprintComm c (n+4))

data Prog = Prog { read :: Var
                 , prg  :: Comm
                 , write :: Var
                 }
    deriving Eq

instance Show Prog where
    show = show . pprintProg

-- Operador para secuencia
infixr 7 <.>
(<.>) :: Comm -> Comm -> Comm
c1 <.> c2 = Seq c1 c2


nextFreeVar :: Prog -> Var
nextFreeVar = (+1) . maximum . vars

vars :: Prog -> [Var]
vars p = nub ([read p, write p] ++ commvars (prg p))

commvars :: Comm -> [Var]
commvars (Assgn v e) = v : exprvars e
commvars (Seq c1 c2) = commvars c1 ++ commvars c2
commvars (While e c) = exprvars e ++ commvars c
