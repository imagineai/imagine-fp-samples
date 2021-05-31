module Parser.Statement where

import Parser.Expr  ( ParserM
                    , parseExpr
                    , parseId
                    , parseLocation, parseMethodCall
                    )
import Parser.Lexer ( pReserved, pSymbol
                    , pNat
                    , pParens, pBrackets, pBraces
                    , pSemi, pComma
                    , pCommaSep1
                    )

import Syntax.Expr ( Expr'(Loc,BOp)
                   , Expr
                   , Location
                   , ArithOp(Plus,Min), BinOp(Arith)
                   , NoInfo(..)
                   )
import Syntax.Statement ( Statement'(..)
                        , Statement
                        , Block'(..)
                        , Block
                        , FieldDecl(..), IdDecl(..)
                        )
import Syntax.Type ( Type(..) )

import Control.Arrow       ( (&&&) )
import Control.Applicative ( pure, (<$), (<$>), (<*>), (<*), (<**>) )

import Text.Parsec ( (<|>)
                   , try, choice, many
                   , optionMaybe
                   )

parseAssign :: ParserM Statement
parseAssign = mkAssign <$> parseLocation <*> parseSymExpr <* pSemi
    where
        mkAssign :: Location -> (Maybe ArithOp, Expr) -> Statement
        mkAssign l (Nothing, e) = Assign l e
        mkAssign l (Just aop, e) = Assign l $ BOp NI (Arith aop) (Loc l) e
        parseSymExpr :: ParserM (Maybe ArithOp, Expr)
        parseSymExpr = 
             (const Nothing &&& id)     <$ pSymbol "="  <*> parseExpr
         <|> (const (Just Plus) &&& id) <$ pSymbol "+=" <*> parseExpr
         <|> (const (Just Min) &&& id)  <$ pSymbol "-=" <*> parseExpr

parseMCall :: ParserM Statement
parseMCall = SMCall <$> parseMethodCall <* pSemi

parseIf :: ParserM Statement
parseIf = If <$  pReserved "if"
             <*> pParens parseExpr 
             <*> parseStatement <*> mparseStatement
    where
        mparseStatement :: ParserM (Maybe Statement)
        mparseStatement = Just <$ pReserved "else" <*> parseStatement
                       <|> pure Nothing

parseFor :: ParserM Statement
parseFor = For <$  pReserved "for"
               <*> parseId   <* pSymbol "="
               <*> parseExpr <* pComma
               <*> parseExpr <*> parseStatement

parseWhile :: ParserM Statement
parseWhile = While <$  pReserved "while"
                   <*> parseExpr <*> parseStatement

parseReturn :: ParserM Statement
parseReturn = Return <$  pReserved "return" <*> mparseExpr <* pSemi
    where
        mparseExpr :: ParserM (Maybe Expr)
        mparseExpr =  optionMaybe $ try parseExpr

parseBreak :: ParserM Statement
parseBreak = Break <$ pReserved "break" <* pSemi

parseContinue :: ParserM Statement
parseContinue = Continue <$ pReserved "continue" <* pSemi

parseSkip :: ParserM Statement
parseSkip = Skip <$ pSemi

parseStatement :: ParserM Statement
parseStatement = choice $ 
                 map try [ parseAssign
                         , parseMCall
                         , parseIf
                         , parseFor
                         , parseWhile
                         , parseReturn
                         , parseBreak
                         , parseContinue
                         , parseSkip
                         , Blck <$> parseBlock
                         ]

parseBlock :: ParserM Block
parseBlock = uncurry Block <$>
             pBraces ((,) <$> many parseFieldDecl <*> many parseStatement)

parseIdDecl :: ParserM IdDecl
parseIdDecl =  parseId <**> (flip Arr <$> pBrackets pNat <|> pure Id)

parseFieldDecl :: ParserM FieldDecl
parseFieldDecl = try $ 
                 FieldDecl <$> parseType <*> pCommaSep1 parseIdDecl <* pSemi

parseType :: ParserM Type
parseType = choice $ 
            map try [ parseIntType
                    , parseFloatType
                    , parseBoolType
                    , parseStringType
                    , parseVarType
                    ]

parseIntType :: ParserM Type
parseIntType = IntType <$ pReserved "int"

parseFloatType :: ParserM Type
parseFloatType = FloatType <$ pReserved "float"

parseBoolType :: ParserM Type
parseBoolType = BoolType <$ pReserved "boolean"

parseStringType :: ParserM Type
parseStringType = StringType <$ pReserved "string"

parseVarType :: ParserM Type
parseVarType = VType <$> parseId
