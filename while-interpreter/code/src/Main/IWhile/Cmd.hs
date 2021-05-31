module Main.IWhile.Cmd where

import System.FilePath.Posix ( takeExtension , takeBaseName )

import Main.IWhile.Monad

import Data.Tree.Pretty ( drawVerticalTreeWith )

import Value       ( Value, vToNat, valueToTree, printAsLList )
import Eval        ( evalProg )
import Parser      ( parserProgFromFile , parserValue )
import ProgAsValue ( progToValue , valueToProg )

data Cmd = Cmd { cmdName :: String
               , args    :: [Arg]
               , action  :: [String] -> IStateM ()
               }

instance Show Cmd where
    show cmd = unwords (cmdName cmd : map show (args cmd))

data Arg = Choice [String] | Param String

cmdNameList :: [String]
cmdNameList = map cmdName cmdList

outFormats :: [String]
outFormats = [ fProg, fTree, fValue, fNat, fList ]

fProg, fTree, fValue, fNat, fList :: String
fProg  = "prog"
fTree  = "tree"
fValue = "data"
fNat   = "nat"
fList  = "list"

instance Show Arg where
    show (Choice [o])         = "[ " ++ o ++ " ]"
    show (Choice opts) = foldl (\str o -> str ++ o ++ " | ") "[ " (init opts) 
                         ++ (last opts ++ " ]")
    show (Param s)            = "<" ++ s ++ ">"

cmdList :: [Cmd]
cmdList = [ loadP
          , loadD
          , showP
          , showD
          , run
          , help
          , append
          , reload
          , quit
          ]

loadP :: Cmd
loadP = Cmd { cmdName = "lp" 
            , args    = [ Param "progfile" ]
            , action  = actionLoadP . head
            }

actionLoadP :: String -> IStateM ()
actionLoadP fp = io (parserProgFromFile fp) >>=
                 either showError (`updateProg` fp)

loadD :: Cmd
loadD = Cmd { cmdName = "ld" 
            , args    = [ Param "value" ]
            , action  = actionLoadD . head
            }

loadData :: String -> IO (Either String (Value,ValueName))
loadData str =
    -- Primero pruebo parsear un valor
    case parserValue str of
         Left _  -> loadFromFileData str
         Right v -> return $ Right (v,"dato")
         
loadFromFileData :: FilePath -> IO (Either String (Value,ValueName))
loadFromFileData fname = 
    case takeExtension fname of
         ".data" -> readFile fname >>= \str ->
                    case parserValue str of
                         Left er -> return $ Left (show er)
                         Right v -> return $ Right (v,vname)
         _       -> parserProgFromFile fname >>= \pres ->
                    case pres of
                         Left er -> return $ Left er
                         Right p -> return $ Right (progToValue p,vname)
    where vname :: ValueName
          vname = takeBaseName fname

actionLoadD :: String -> IStateM ()
actionLoadD str = io (loadData str) >>= either showError (uncurry updateData)

showprog :: String -> IStateM ()
showprog format = whenProg (showMsg . (++) "Programa cargado: \n\n" . swProg)
    where swProg :: LoadedProg -> String
          swProg lp = let p = lProg lp in
                      if format == fProg
                      then show p
                      else outFormat format $ progToValue p

showP :: Cmd
showP = Cmd { cmdName = "showp" 
            , args    = [ Choice outFormats ]
            , action  = showprog . head
            }

showdata :: String -> IStateM ()
showdata format = 
    whenData (\(d,_) -> showMsg ("Dato cargado: \n\n" ++
             outFormat format d))

outFormat :: String -> Value -> String
outFormat f d | f == fProg = maybe "El dato no es un programa" 
                                  show (valueToProg d)
              | f == fTree = drawVerticalTreeWith 1 $ 
                            valueToTree d
              | f == fValue = show d
              | f == fNat = maybe "El dato no es un natural" show (vToNat d)
              | f == fList = printAsLList d
              | otherwise = error $ "Imposible: outFormat " ++ f

showD :: Cmd 
showD = Cmd { cmdName = "showd"
            , args = [ Choice outFormats ]
            , action = showdata . head
            }

run :: Cmd
run = Cmd { cmdName = "run" 
          , args    = [ Choice outFormats ]
          , action  = runp . head
          }

runp :: String -> IStateM ()
runp outformat = 
    whenProg (\lp -> whenData (\(d,_) ->
    case evalProg (lProg lp) d of
         Left e -> showError (show e)
         Right v -> showMsg ("Resultado:\n\n" ++ showout v)
    ))
    where showout :: Value -> String
          showout = outFormat outformat

help :: Cmd
help = Cmd { cmdName = "help"
           , args    = []
           , action  = const showHelp
           }

showHelp :: IStateM ()
showHelp = showMsg $
            unlines $ [ ""
                      , "Comandos disponibles: "
                      , ""
                      ] ++ map ((++) "\t" . show) cmdList

append :: Cmd
append = Cmd { cmdName = "append"
             , args    = [ Param "value" ]
             , action  = appendD . head
             }

appendD :: String -> IStateM ()
appendD str = io (loadData str) >>= either showError (uncurry appendData)

quit :: Cmd
quit = Cmd { cmdName = "quit" 
           , args    = []
           , action  = const $ io $ return ()
           }

reload :: Cmd
reload = Cmd { cmdName = "r"
             , args    = []
             , action  = const reloadD
             }

reloadD :: IStateM ()
reloadD = getProg >>= 
          maybe (showError "Ningún programa cargado") (actionLoadP . fpProg) 
