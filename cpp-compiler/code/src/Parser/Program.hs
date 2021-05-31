module Parser.Program where

import Parser.Lexer ( pReserved
                    , pSemi
                    , pParens, pBraces
                    , pCommaSep
                    )
import Parser.Expr ( ParserM
                   , parseId
                   )
import Parser.Statement ( parseType, parseBlock, parseFieldDecl )

import Syntax.Program ( Program
                      , ClassDecl'(..)
                      , ClassDecl
                      , MethodDecl'(..)
                      , MethodDecl
                      , ParamDecl(..)
                      , Body'(..)
                      , Body
                      )

import Text.Parsec ( (<|>), many, many1 )

import Control.Applicative ( (<$), (<$>), (<*>), (<*) )

parseParamDecl :: ParserM ParamDecl
parseParamDecl = Param <$> parseType <*> parseId

parseBody :: ParserM Body
parseBody =   Local <$> parseBlock
          <|> Extern <$ pReserved "extern" <* pSemi

parseMethodDecl :: ParserM MethodDecl
parseMethodDecl = 
        Fun <$> parseType <*> parseId <*> 
                pParens (pCommaSep parseParamDecl) <*>
                parseBody
    <|> Proc <$ pReserved "void" <*> parseId <*>
                pParens (pCommaSep parseParamDecl) <*>
                parseBody
            

parseClassDecl :: ParserM ClassDecl
parseClassDecl = uncurry . ClassDecl <$ pReserved "class" <*> parseId <*>
                 pBraces ((,) <$> many parseFieldDecl <*> many parseMethodDecl)
            
parseProgram :: ParserM Program
parseProgram = many1 parseClassDecl
