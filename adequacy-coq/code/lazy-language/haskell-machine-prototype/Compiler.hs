module Compiler where

import Source  ( Term (..) )
import Machine ( Val (..), Code (..) )
import qualified Source  as T ( Term (Pair, Let, Fst, Snd) )
import qualified Machine as M ( Val (Pair), Code (Let, Fst, Snd) )

compile :: Term -> Code
compile Unit              = V U
compile (Idx n)           = A n
compile (Num m)           = V $ C m
compile (Lam t)           = V $ Grab $ compile t
compile (App t n)         = Push n $ compile t
compile (T.Let t t')      = M.Let (Rec $ compile t) $ compile t'
compile (T.Pair t t')     = V $ M.Pair (compile t) (compile t')
compile (T.Fst n)         = M.Fst n
compile (T.Snd n)         = M.Snd n
compile (BinOp bop t t')  = BOp bop (compile t) (compile t')
compile (IfZero t t' t'') = IfZ (compile t) (compile t') (compile t'')
