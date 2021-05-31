module Parser.Expr where

import Syntax.Expr ( Expr'(..)
                   , Expr
                   , Identifier
                   , Field' (..)
                   , Field
                   , Location'(..), MethodCall'(..)
                   , Location, MethodCall
                   , Literal(..)
                   , BinOp(..), ArithOp(..), RelOp(..)
                   , EqOp(..), CondOp(..), UnOp(..)
                   , NoInfo(..)
                   )

import Parser.Lexer ( pReservedOp, pReserved
                    , pIdentifier, pNat, pFloat, pStringLiteral
                    , pParens, pBrackets
                    , pDot, pCommaSep
                    )

import Control.Monad          ( liftM )
import Control.Applicative    ( (<$), (<$>), (<**>), pure)
import Control.Monad.Identity ( Identity )

import Text.Parsec      ( Parsec, (<|>), (<?>), try, sepBy1 )
import Text.Parsec.Expr ( buildExpressionParser
                        , Operator(Infix,Prefix), OperatorTable, Assoc(AssocLeft)
                        )
import Text.Parsec.Combinator ( choice )

-- Mónada de parser
type ParserM a = Parsec String () a

type Op a = Operator String () Identity a
type OpTable a = OperatorTable String () Identity a

opTable :: OpTable Expr
opTable = prefixOps ++ arithOps ++ relOps ++ eqOps ++ boolOps

prefixOps :: [[Op Expr]]
prefixOps = [ [prefix "-" Neg]
            , [prefix "!" Not]
            ]

arithOps :: [[Op Expr]]
arithOps = [ [ binary "*" (Arith Prod) AssocLeft
             , binary "/" (Arith Div) AssocLeft
             , binary "%" (Arith Mod) AssocLeft
             ]
           , [ binary "+" (Arith Plus) AssocLeft
             , binary "-" (Arith Min) AssocLeft
             ]
           ]

relOps :: [[Op Expr]]
relOps = [ [ binary "<"  (Rel Lt)  AssocLeft
           , binary ">"  (Rel Gt)  AssocLeft
           , binary "<=" (Rel Leq) AssocLeft
           , binary ">=" (Rel Geq) AssocLeft
           ]
         ]

eqOps :: [[Op Expr]]
eqOps = [ [ binary "==" (Eq Equal)  AssocLeft
          , binary "!=" (Eq NEqual) AssocLeft
          ]
        ]

boolOps :: [[Op Expr]]
boolOps = [ [ binary "&&" (Cond And) AssocLeft ]
          , [ binary "||" (Cond Or)  AssocLeft ]
          ]

binary :: String -> BinOp -> Assoc -> Op Expr
binary op con = Infix (BOp NI con <$ pReservedOp op)

prefix :: String -> UnOp -> Op Expr
prefix op con = Prefix (UOp NI con <$ pReservedOp op)


-- Parser Location
parseId :: ParserM Identifier
parseId = pIdentifier

parseField :: ParserM Field
parseField = parseId <**> (mkFIdArray <$> pBrackets parseExpr <|> pure (FId NI))
    where 
        mkFIdArray :: Expr -> String -> Field
        mkFIdArray = flip $ FIdArray NI

parseLocation :: ParserM Location
parseLocation = mkLoc <$> sepBy1 parseField pDot
    where 
        mkLoc :: [Field] -> Location
        mkLoc [] = error "Impossible"
        mkLoc (f:fs) = foldl LApp (LBase f) fs
              
-- Parser Method Call
parseMethodCall :: ParserM MethodCall
parseMethodCall = parseLocation >>= \l ->
    case l of
         (LBase (FId _ _)) -> liftM (MethodCall l) parseArgs
         (LApp _ (FId _ _)) -> liftM (MethodCall l) parseArgs
         _ -> fail "unexpected '('"
    where 
        parseArgs ::ParserM [Expr]
        parseArgs = pParens $ pCommaSep expr

parseLiteral :: ParserM Literal
parseLiteral =  try (FloatL <$> pFloat)
            <|> IntL   <$> pNat
            <|> BoolL True  <$  pReserved "true"
            <|> BoolL False <$  pReserved "false"
            <|> StringL     <$> pStringLiteral

expr :: ParserM Expr
expr = choice 
       ( map try 
         [ MCall <$> parseMethodCall
         , Loc   <$> parseLocation
         , Lit   NI <$> parseLiteral
         ]
       ) <|> pParens expr
       <?> "expresión"

parseExpr :: ParserM Expr
parseExpr = try (buildExpressionParser opTable expr)
            <|> pParens parseExpr
