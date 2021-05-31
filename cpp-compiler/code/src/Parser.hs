module Parser where

import Syntax ( Program, Statement, Expr, pprintProgram )

import Parser.Expr      ( parseExpr      )
import Parser.Program   ( parseProgram   )
import Parser.Statement ( parseStatement )

import Control.Applicative ((<*))

import Text.Parsec ( runParser, eof, ParseError )

parseFromString :: String -> Either ParseError Program
parseFromString = runParser (parseProgram <* eof) () ""

parseEFromString :: String -> Either ParseError Expr
parseEFromString = runParser (parseExpr <* eof) () ""

parseSFromString :: String -> Either ParseError Statement
parseSFromString = runParser (parseStatement <* eof) () ""

parseFromFile :: FilePath -> IO ()
parseFromFile fp = readFile fp >>= 
                   either print (print . pprintProgram) . parseFromString
