module Parser.ParserProg ( parserBaseProg
                         , parserExtProg
                         , parserProgFromFile ) where

import qualified Parser.ParserBase as PBase
import qualified Parser.ParserExt as PExt
import System.FilePath.Posix ( takeExtension )
import Prog
import ExtendedLanguage.ExtLanguage
import ExtendedLanguage.Compiler

import Text.Parsec

parserBaseProg :: String -> Either ParseError Prog
parserBaseProg = runParser pBaseProg PBase.initState ""
    where pBaseProg = PBase.pProg >>= \bp ->
                      eof >> return bp

parserExtProg :: String -> Either ParseError (ExtProg,ProgNames)
parserExtProg = runParser pExtProg PExt.initState ""
    where pExtProg = PExt.pProgs >>= \ep ->
                     eof >> return ep

parserProgFromFile :: FilePath -> IO (Either String Prog)
parserProgFromFile fname =
    case takeExtension fname of
         ".while"  -> readFile fname >>=
                        either (return . Left . show) (return . Right) 
                               . parserBaseProg
         ".xwhile" -> readFile fname >>= 
                      either (return . Left . show) compile . parserExtProg
         _         -> return $ Left "Extensión de archivo no válida."
    where compile :: (ExtProg, ProgNames) -> IO (Either String Prog)
          compile = either (return . Left . show) (return . Right) .
                           uncurry compileEProg
