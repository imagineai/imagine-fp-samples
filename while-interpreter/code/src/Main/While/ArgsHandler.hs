module Main.While.ArgsHandler where

import Eval   ( EvalError )
import Prog   ( Prog  )
import Value  ( Value, valueToTree )
import Parser ( parserBaseProg, parserExtProg, parserValue )
import ProgAsValue ( progToValue, valueToProg )
import ExtendedLanguage.ExtLanguage ( ExtProg, ProgNames )
import ExtendedLanguage.Compiler ( compileEProg )

import Data.Tree.Pretty      ( drawVerticalTreeWith )
import Text.Parsec.Error     ( ParseError )
import System.IO.Error       ( tryIOError )
import System.Console.GetOpt ( OptDescr( Option )
                             , ArgDescr( NoArg, ReqArg )
                             , ArgOrder( Permute )
                             , getOpt, usageInfo
                             )
import System.FilePath.Posix ( takeExtension )
import Control.Applicative   ( (<$>) )

type ParsedOptions = ([Options -> Options], [String] , [String])

data MainOption = Translate | Execute

data ProgType = Base | Extended

data OutMode = AsProg | AsData | AsRawData

data Options = Options { optMainOption :: MainOption
                       , optProgType   :: ProgType
                       , optOutMode    :: OutMode
                       , optProgFile   :: Maybe FilePath
                       , optInputFile  :: Maybe FilePath
                       }

defaultOptions :: Options
defaultOptions = Options { optMainOption  = Execute
                         , optProgType    = Base
                         , optOutMode     = AsData
                         , optProgFile    = Nothing
                         , optInputFile   = Nothing
                         }

options :: [OptDescr (Options -> Options)]
options = 
        [ Option "b" ["base"]
                (NoArg (\opt -> opt {optProgType = Base}))     ""
        , Option "x" ["extended"]
                (NoArg (\opt -> opt {optProgType = Extended})) ""
        , Option [] ["pd","program-as-data"]
                (NoArg (\opt -> opt {optMainOption = Translate})) ""
        , Option [] ["op", "output-as-prog"]
                (NoArg (\opt -> opt {optOutMode  = AsProg}))   ""
        , Option [] ["od", "output-as-data"]
                (NoArg (\opt -> opt {optOutMode  = AsData}))   ""
        , Option [] ["rod", "output-as-raw-data"]
                (NoArg (\opt -> opt {optOutMode  = AsRawData})) ""
        , Option "p" ["program"]
                (genReqArg (\file opt -> opt {optProgFile  = Just file})) ""
        , Option "i" ["program-input"]
                (genReqArg (\file opt -> opt {optInputFile = Just file})) ""
        ]
    where
        genReqArg :: (String -> Options -> Options) ->
                    ArgDescr (Options -> Options)
        genReqArg f = ReqArg f "FILE"

usage :: String
usage = usageInfo "Usage" options

checkArgs :: [String] -> IO (Either IOError Options)
checkArgs args = tryIOError $ checkOpts (getOpt Permute options args)

checkOpts :: ParsedOptions -> IO Options
checkOpts (opts, _, []) = return $ foldl (flip id) defaultOptions opts
checkOpts (_, _, errs)  = ioError $ userError $ concat errs ++ usage

printError :: ParseError -> IO a
printError pe = ioError $ userError $ show pe

printErrorProg :: ParseError -> IO a
printErrorProg pe = putStrLn "Programa invalido: " >>
                    printError pe

printErrorData :: ParseError -> IO a
printErrorData pe = putStrLn "Dato invalido: " >> 
                    printError pe

parseFileProg :: ProgType -> Maybe FilePath -> IO Prog
parseFileProg _ Nothing      = ioError $ userError usage
parseFileProg Base (Just fp) = 
                         readFile fp >>= \str -> 
                         case parserBaseProg str of
                              Left err   -> printErrorProg err
                              Right prog -> return prog
parseFileProg Extended (Just fp) = 
              readFile fp >>= either printErrorProg compile . parserExtProg
    where
        compile :: (ExtProg, ProgNames) -> IO Prog
        compile = either (ioError . userError) return . uncurry compileEProg

parseFileInput :: Maybe FilePath -> IO Value
parseFileInput Nothing   = ioError $ userError usage
parseFileInput (Just fp) | takeExtension fp == ".while" =
                           progToValue <$> parseFileProg Base (Just fp)
                         | otherwise = 
                           readFile fp >>= \str -> 
                           case parserValue str of
                               Left err  -> printErrorData err
                               Right val -> return val

printOutput :: Either EvalError Value -> OutMode -> IO ()
printOutput (Left err) _     = putStrLn err
printOutput (Right v) AsRawData = print v
printOutput (Right v) AsData = printOP $ drawVerticalTreeWith 1 $ valueToTree v
printOutput (Right v) AsProg = printOP $ printVasP $ valueToProg v
    where
        printVasP :: Maybe Prog -> String
        printVasP (Just p) = show p
        printVasP Nothing  = unwords [ "El valor resultado no "
                                     , "se corresponde con un programa"
                                     ]

printOP :: String -> IO ()
printOP str = putStrLn $ unlines [ ""
                                 , "Resultado:"
                                 , ""
                                 , ""
                                 , str
                                 ]
