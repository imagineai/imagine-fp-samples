{-# LANGUAGE RankNTypes #-}
module Parser.ParserBase ( PStateWhile (..)
                         , VarNames
                         , ParserW
                         , PState (..)
                         , initState
                         , keywordsBase
                         , langBase
                         , identifier
                         , reserved
                         , reservedOp
                         , parens
                         , semi
                         , white
                         , comma
                         , brackets
                         , symbol
                         , braces
                         , colon
                         , pExpr
                         , pExpr'
                         , pvar
                         , pProg
                         , resetStateVars) where

import Expr
import Prog
import Value

import Text.Parsec
import Text.Parsec.Language (emptyDef)
import qualified Text.Parsec.Token as P
import qualified Data.Map as M
import Control.Applicative ( (<$), (<$>), (<*>), (<*) )

-- Mapa de nombres de variables
type VarNames = M.Map String Var

-- Clase del estado de un parser de while.
-- Permite tener parsers incrementales
class PStateWhile p where
    getMaxv  :: p -> Int
    getMapv  :: p -> VarNames
    getLexer :: PStateWhile p => p -> P.TokenParser p
    setMaxv  :: Int -> p -> p
    setMapv  :: VarNames -> p -> p
    setLexer :: PStateWhile p => P.TokenParser p -> p -> p
    

-- Estado del parser, para calcular el indice que corresponde
-- a cada variable. 
data PState = PState { maxv :: Int
                     , mapv :: M.Map String Var
                     -- Lexer. No se modifica.
                     , lexer :: P.TokenParser PState
                     }
                     
instance PStateWhile PState where
    getMaxv       = maxv
    getMapv       = mapv
    getLexer      = lexer
    setMaxv v st  = st { maxv = v }
    setMapv m st  = st { mapv = m }
    setLexer l st = st { lexer = l }
                     
initState :: PState
initState = PState 0 M.empty lexerBase
                     
-- Mónada de parser
type ParserW p a = Parsec String p a

resetStateVars :: PStateWhile p => ParserW p ()
resetStateVars = modifyState (setMaxv 0) >>
                 modifyState (setMapv M.empty)

-- Palabras reservadas
keywordsBase :: [String]
keywordsBase = 
           [ "cons"
           , "hd"
           , "tl"
           , "while"
           , "do"
           , "od"
           , "read"
           , "write"
           , "nil"
           , "univ"
           , "*"
           ]

langBase :: forall u . P.LanguageDef u
langBase = emptyDef { P.commentStart  = "(*"
                    , P.commentEnd    = "*)"
                    , P.identStart    = letter
                    , P.identLetter   = alphaNum <|> char '_'
                    , P.opStart       = oneOf ":="
                    , P.opLetter      = oneOf "?="
                    , P.reservedNames = keywordsBase
                    }

lexerBase :: P.TokenParser u
lexerBase = P.makeTokenParser langBase

identifier :: PStateWhile p => ParserW p String
identifier = getState >>= P.identifier . getLexer

reserved :: PStateWhile p => String -> ParserW p ()
reserved s = getState >>= \l -> (P.reserved $ getLexer l) s

reservedOp :: PStateWhile p => String -> ParserW p ()
reservedOp s = getState >>= \l -> (P.reservedOp $ getLexer l) s

parens :: PStateWhile p => ParserW p a -> ParserW p a
parens p = getState >>= \st -> (P.parens $ getLexer st) p

semi :: PStateWhile p => ParserW p String
semi = getState >>= P.semi . getLexer

white :: PStateWhile p => ParserW p ()
white = getState >>= P.whiteSpace . getLexer

comma :: PStateWhile p => ParserW p String
comma = getState >>= P.comma . getLexer

brackets :: PStateWhile p => ParserW p a -> ParserW p a
brackets p = getState >>= \l -> (P.brackets $ getLexer l) p

symbol :: PStateWhile p => String -> ParserW p String
symbol s = getState >>= \l -> (P.symbol $ getLexer l) s

colon :: PStateWhile p => ParserW p String
colon = getState >>= P.colon . getLexer

braces :: PStateWhile p => ParserW p a -> ParserW p a
braces p = getState >>= \l -> (P.braces $ getLexer l) p

-- Parser de expresiones. Toma como parámetro un parser
-- de expresiones para posibles extensiones.
pExpr' :: PStateWhile p => ParserW p Expr -> ParserW p Expr
pExpr' pext = choice (map try 
                     [ pext
                     , V <$> pvar
                     , patom 
                     , pcons pext 
                     , phd pext
                     , ptl pext
                     , peq pext
                     , pstar 
                     , puniv pext
                     ])
           <|> parens (pExpr' pext)
           <?> "expresión"

pExpr :: PStateWhile p => ParserW p Expr
pExpr = pExpr' parserZero
         
pvar :: PStateWhile p => ParserW p Var
pvar = identifier >>= \v -> getState >>= \st ->
       maybe (upd v >> getMaxv <$> getState)
             return (M.lookup v $ getMapv st)
    where upd v = modifyState (addVar v)
          addVar :: PStateWhile p => String -> p -> p
          addVar s pst = let newmaxv = getMaxv pst + 1 in
                             setMapv (M.insert s newmaxv (getMapv pst))
                                     (setMaxv newmaxv pst)

patom :: PStateWhile p => ParserW p Expr
patom = A Nil <$ reserved "nil"

pcons :: PStateWhile p => ParserW p Expr -> ParserW p Expr
pcons pext = Cons <$ reserved "cons" <*> pExpr' pext <*> pExpr' pext

phd :: PStateWhile p => ParserW p Expr -> ParserW p Expr
phd pext = Hd <$ reserved "hd" <*> pExpr' pext

ptl :: PStateWhile p => ParserW p Expr -> ParserW p Expr
ptl pext = Tl <$ reserved "tl" <*> pExpr' pext

peq :: PStateWhile p => ParserW p Expr -> ParserW p Expr
peq pext = Eq <$ reservedOp "=?" <*> pExpr' pext <*> pExpr' pext

pstar :: PStateWhile p => ParserW p Expr
pstar = Star <$ reserved "*"

puniv :: PStateWhile p => ParserW p Expr -> ParserW p Expr
puniv pext = Univ <$ reserved "univ" <*> pExpr' pext <*> pExpr' pext

-- Parser de comandos simples
pSimpleComm :: PStateWhile p => ParserW p Comm
pSimpleComm = choice (map try [ passign, pwhile]) <?> "comando"

pComm :: PStateWhile p => ParserW p Comm
pComm =  foldr1 Seq <$> sepEndBy1 pSimpleComm semi
     <|> parens pComm
        
passign :: PStateWhile p => ParserW p Comm
passign = Assgn <$> pvar <* reservedOp ":=" <*> pExpr

pwhile :: PStateWhile p => ParserW p Comm
pwhile = While <$ 
         reserved "while" <*> pExpr <* reserved "do" <*> pComm <* reserved "od"

-- Parser de programas
pProg :: PStateWhile p => ParserW p Prog
pProg = Prog <$ white <* 
        reserved "read" <*> pvar <* semi <*>
        pComm <*
        reserved "write" <*> pvar <* semi
