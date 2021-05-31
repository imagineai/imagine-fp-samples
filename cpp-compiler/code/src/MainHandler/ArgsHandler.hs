module MainHandler.ArgsHandler where

import Text.Parsec.Error     ( ParseError )
import System.IO.Error       ( tryIOError )
import System.Console.GetOpt ( OptDescr( Option )
                             , ArgDescr( NoArg, ReqArg )
                             , ArgOrder( Permute )
                             , usageInfo, getOpt
                             )

type ParsedOptions = ([Options -> Options], [String] , [String])

data Phase = UnknownPhase String
           | Parse | StaticCheck | CodInter | Assembly | Executable
     deriving Show

type Help = Bool

data Options = Options { optInName :: Maybe FilePath
                       , optOutName :: Maybe FilePath
                       , optTarget  :: Phase
                       , optHelp    :: Help
                       }
     deriving Show

defaultOptions :: Options
defaultOptions = Options { optInName  = Nothing
                         , optOutName = Nothing
                         , optTarget  = Executable
                         , optHelp    = False
                         }

missingIFmsg :: String
missingIFmsg = "Falta el archivo de entrada"

inMsg :: String
inMsg = "Nombre del archivo de <entrada>"

outMsg :: String
outMsg = "Renombra el archivo ejecutable a <salida>"

targetMsg :: String
targetMsg = unlines [ unwords [ "<etapa> es una de \"parse\", \"staticcheck\","
                              , "\"codinter\", \"assembly\" o \"executable\"."
                              ]
                    , "La compilación procede hasta la etapa dada."
                    ]

optzMsg :: String 
optzMsg = unlines 
          [ "Realiza la lista de optimizaciones (separadas por coma)."
          , "incluir \"all\", realiza todas las optimizaciones soportadas."
          ]

debugMsg :: String
debugMsg = unlines [ "Imprime información de debugging. Si la"
                   , "opción no es dada, cuando la compilación es"
                   , "exitosa no debería imprimirse ninguna salida."
                   ]

helpMsg :: String
helpMsg = "Muestra la información actual."

options :: [OptDescr (Options -> Options)]
options = 
        [ Option "i" ["input"] 
          (ReqArg (\fn opt -> opt {optInName = Just fn}) "<entrada>")
          inMsg
        , Option "o" ["output"] 
          (ReqArg (\fn opt -> opt {optOutName = Just fn}) "<salida>")
          outMsg
        , Option "t" ["target"]
          (ReqArg (\t opt -> opt {optTarget = UnknownPhase t}) "<etapa>")
          targetMsg
        , Option "h" ["help"]
          (NoArg (\opt -> opt {optHelp = True}))
          helpMsg
        {- ##### Opciones no implementadas #####
        , Option [] ["opt"]
          (ReqArg (\o opt -> opt {optOptz = [UnknownOptz o]}) "[optimización]")
          optzMsg
        , Option [] ["debug"]
          (NoArg (\opt -> opt {optDebug = True}))
          debugMsg
        -}
        ]

usage :: String
usage = usageInfo cmdMsg options
   where
       cmdMsg :: String
       cmdMsg = unlines [ ""
                        , "Uso: "
                        , "compi [opciones] \"nombreArchivo\".compi"
                        , ""
                        , "Optiones: "
                        ]

checkArgs :: [String] -> IO (Either IOError Options)
checkArgs args = tryIOError (checkOpts (getOpt Permute options args) >>=
                            \opts -> checkInputFile (optInName opts) >>
                            return opts)

checkInputFile :: Maybe FilePath -> IO ()
checkInputFile Nothing = ioError $ userError err 
    where
        err :: String
        err = unlines [ ""
                      , missingIFmsg
                      , usage
                      ]
checkInputFile _ = return ()

checkOpts :: ParsedOptions -> IO Options
checkOpts (opts, _, []) = secondCheckOpts $ foldl (flip id) defaultOptions opts
checkOpts (_, _, errs)  = ioError $ userError $ concat errs ++ usage

secondCheckOpts :: Options -> IO Options
secondCheckOpts opts | optHelp opts = ioError $ userError usage
                     | otherwise = checkPhase opts

checkPhase :: Options -> IO Options
checkPhase opt = do p <- parsePhase $ optTarget opt
                    return $ opt {optTarget = p}

parsePhase :: Phase -> IO Phase
parsePhase (UnknownPhase "parse")       = return Parse
parsePhase (UnknownPhase "staticcheck") = return StaticCheck
parsePhase (UnknownPhase "codinter")    = return CodInter
parsePhase (UnknownPhase "assembly")    = return Assembly
parsePhase (UnknownPhase "executable")  = return Executable
parsePhase (UnknownPhase unkwnonPhase)  = ioError $ userError err 
    where
        unkPhase :: String
        unkPhase = "Etapa \"" ++ unkwnonPhase ++ "\" desconocida"
        err :: String
        err = unlines [ unkPhase
                      , usage
                      ]
parsePhase p = return p

printError :: ParseError -> IO a
printError pe = ioError $ userError $ show pe
