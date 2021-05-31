module ProgAsValue ( progToValue
                   , valueToProg
                   , dvar, dquote
                   , dcons, dhd
                   , dtl, deq
                   , dstar, duniv
                   , dassign, dseq, dwhile
                   ) where

import Prog
import Value
import Expr

import Control.Applicative

{- Representación de los programas en el conjunto de valores.
   Para cada construcción del lenguaje tendremos un elemento
   único en Value. Definición 3.2.1 del libro. -}

-- Conversión de programa a valor --
progToValue :: Prog -> Value
progToValue (Prog i comm o) = consStar [ consStar [dvar,iToV i]
                                       , commToValue comm
                                       , consStar [dvar,iToV o]
                                       ]
    
commToValue :: Comm -> Value
commToValue (Assgn v e) = consStar [dassign,
                                    consStar [dvar,iToV v], 
                                    exprToValue e]
commToValue (Seq c d)   = consStar [dseq, commToValue c, commToValue d]
commToValue (While e c) = consStar [dwhile, exprToValue e, commToValue c]
    
exprToValue :: Expr -> Value
exprToValue = consStar . exprToValue'

exprToValue' :: Expr -> [Value]
exprToValue' (V v)      = [dvar,iToV v]
exprToValue' (A at)     = [dquote, VAtom at]
exprToValue' (Cons e f) = [dcons, exprToValue e, exprToValue f]
exprToValue' (Hd e)     = [dhd, exprToValue e]
exprToValue' (Tl e)     = [dtl, exprToValue e]
exprToValue' (Eq e f)   = [deq, exprToValue e, exprToValue f]
exprToValue' Star       = [dstar]
exprToValue' (Univ e f) = [duniv, exprToValue e, exprToValue f]


-- Elementos en Value para diferenciar cada palabra clave del lenguaje
dvar :: Value
dvar = iToV (-1)

dassign :: Value
dassign = iToV (-2)

dseq :: Value
dseq = iToV (-3)

dwhile :: Value
dwhile = iToV (-4)

dquote :: Value
dquote = iToV (-5)

dcons :: Value
dcons = iToV (-6)

dhd :: Value
dhd = iToV (-7)

dtl :: Value
dtl = iToV (-8)

deq :: Value
deq = iToV (-9)

dstar :: Value
dstar = iToV (-10)

duniv :: Value
duniv = iToV (-11)


-- Conversión de valor a programa --
valueToProg :: Value -> Maybe Prog
valueToProg (Dot v1 (Dot v2 v3)) = 
    -- v1 debe ser la codificación de "read v"
    vVar v1 >>= \readv ->
    valueToComm v2 >>= \c ->
    vVar v3 >>= \writev ->
    return (Prog readv c writev)
valueToProg _ = Nothing
    
valueToComm :: Value -> Maybe Comm
valueToComm v@(Dot _ (Dot _ _)) =
    vAssgn v <|> vSeq v <|> vWhile v
valueToComm _ = Nothing
       
valueToExpr :: Value -> Maybe Expr
valueToExpr v@(Dot _ _) = 
    foldl (\m vm -> m <|> vm v) Nothing 
          [vVarExpr,vQuote,vCons,vHd,vTl,vEq,vStar,vUniv]
valueToExpr _ = Nothing


vVar :: Value -> Maybe Var
vVar (Dot v1 v2) = 
    whenM (v1 == dvar) >> 
    vToNat v2
vVar _ = Nothing

vVarExpr :: Value -> Maybe Expr
vVarExpr v = V <$> vVar v

vAt :: Value -> Maybe Atom
vAt (VAtom Nil) = Just Nil
vAt _ = Nothing

vAssgn :: Value -> Maybe Comm
vAssgn (Dot v1 (Dot v2 v3)) = Assgn <$> 
                              (whenM (v1 == dassign) >> vVar v2) <*>
                              valueToExpr v3
vAssgn (VAtom _) = error "vAssgn: pattern (VAtom _)"
vAssgn (Dot _ (VAtom _)) = error "vAssgn: pattern (Dot _ (VAtom _))"

vSeq :: Value -> Maybe Comm
vSeq (Dot v1 (Dot v2 v3)) = Seq <$>
                            (whenM (v1 == dseq) >> valueToComm v2) <*>
                            valueToComm v3
vSeq (VAtom _) = error "vSeq: pattern (VAtom _)"
vSeq (Dot _ (VAtom _)) = error "vSeq: pattern (Dot _ (VAtom _))"

vWhile :: Value -> Maybe Comm
vWhile (Dot v1 (Dot v2 v3)) = While <$>
                              (whenM (v1 == dwhile) >> valueToExpr v2) <*>
                              valueToComm v3
vWhile (VAtom _) = error "vWhile: pattern (VAtom _)"
vWhile (Dot _ (VAtom _)) = error "vWhile: pattern (Dot _ (VAtom _))"

vQuote :: Value -> Maybe Expr
vQuote (Dot v1 v2) = A <$> (whenM (v1 == dquote) >> vAt v2)
vQuote _ = Nothing

vCons :: Value -> Maybe Expr
vCons (Dot v1 (Dot v2 v3)) = Cons <$>
                             (whenM (v1 == dcons) >> valueToExpr v2) <*>
                             valueToExpr v3
vCons _ = Nothing

vHd :: Value -> Maybe Expr
vHd (Dot v1 v2) = Hd <$> (whenM (v1 == dhd) >> valueToExpr v2)
vHd _ = Nothing

vTl :: Value -> Maybe Expr
vTl (Dot v1 v2) = Tl <$> (whenM (v1 == dtl) >> valueToExpr v2)
vTl _ = Nothing

vEq :: Value -> Maybe Expr
vEq (Dot v1 (Dot v2 v3)) = Eq <$>
                           (whenM (v1 == deq) >> valueToExpr v2) <*>
                           valueToExpr v3
vEq _ = Nothing

vStar :: Value -> Maybe Expr
vStar v = whenM (v == dstar) >> return Star

vUniv :: Value -> Maybe Expr
vUniv (Dot v1 (Dot v2 v3)) = Univ <$> 
                             (whenM (v1 == duniv) >> valueToExpr v2) <*>
                             valueToExpr v3
vUniv _ = Nothing

    
-- Auxiliares
consStar :: [Value] -> Value
consStar [] = nil
consStar ds = foldr1 Dot ds

whenM :: Bool -> Maybe ()
whenM True  = Just ()
whenM False = Nothing
