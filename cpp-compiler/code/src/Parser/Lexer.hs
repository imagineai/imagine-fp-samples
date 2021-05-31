module Parser.Lexer where

import Text.Parsec       ( Parsec, (<|>) )
import Text.Parsec.Char  ( alphaNum
                         , char
                         , oneOf
                         , letter
                         )
import Text.Parsec.Token ( commaSep, commaSep1, semi, comma, dot
                         , stringLiteral, natural, float
                         , braces, brackets, parens
                         , identifier
                         , reserved, reservedOp, symbol
                         , makeTokenParser, TokenParser
                         , LanguageDef, GenLanguageDef(..)
                         )

type ParsecL a = Parsec String () a

keywords :: [String]
keywords = [ "class"
           , "void"
           , "extern"
           , "int", "float", "boolean", "string"
           , "if", "else"
           , "for"
           , "while"
           , "return"
           , "break"
           , "continue"
           , "true"
           , "false"
           ]
            
operators :: [String]
operators = [ "+", "-", "*", "/", "%"
            , "<", ">" , "<=", ">="
            , "==", "!="
            , "&&", "||"
            , "!"
            ]
           

language :: LanguageDef st
language = LanguageDef {
            commentStart    = "/*"
          , commentEnd      = "*/"
          , commentLine     = "//"
          , nestedComments  = True
          , identStart      = letter
          , identLetter     = alphaNum <|> char '_'
          , opStart         = oneOf "+-*/%<>=!&|"
          , opLetter        = oneOf "=&|"
          , reservedNames   = keywords
          , reservedOpNames = operators
          , caseSensitive   = True
}
          
lexer :: TokenParser st
lexer = makeTokenParser language

pSymbol :: String -> ParsecL String
pSymbol = symbol lexer

pReservedOp :: String -> ParsecL ()
pReservedOp = reservedOp lexer

pReserved :: String -> ParsecL ()
pReserved = reserved lexer

pIdentifier :: ParsecL String
pIdentifier = identifier lexer

pParens :: ParsecL a -> ParsecL a
pParens = parens lexer

pBrackets :: ParsecL a -> ParsecL a
pBrackets = brackets lexer

pBraces :: ParsecL a -> ParsecL a
pBraces = braces lexer

pNat :: ParsecL Integer
pNat = natural lexer

pFloat :: ParsecL Double
pFloat = float lexer

pStringLiteral :: ParsecL String
pStringLiteral = stringLiteral lexer

pDot :: ParsecL String
pDot = dot lexer

pComma :: ParsecL String
pComma = comma lexer

pSemi :: ParsecL String
pSemi = semi lexer

pCommaSep :: ParsecL a -> ParsecL [a]
pCommaSep = commaSep lexer

pCommaSep1 :: ParsecL a -> ParsecL [a]
pCommaSep1 = commaSep1 lexer
