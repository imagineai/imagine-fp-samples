module Main where

import Eval        ( evalProg, EvalError )
import Value       ( Value, (·) )
import Prog        ( Prog )
import ProgAsValue ( progToValue )
import Main.While.ArgsHandler
                   ( MainOption (..)
                   , Options
                   , checkArgs
                   , optMainOption, optProgFile, optInputFile
                   , optProgType, optOutMode
                   , parseFileProg, parseFileInput
                   , printOutput
                   )

import Control.Applicative ( (<$>), (<*>) )
import Control.Arrow ( (&&&) )
import System.Environment ( getArgs )
import System.IO.Error    ( catchIOError, ioeGetErrorString )

main :: IO ()
main = getArgs >>= checkArgs >>=
       either (putStrLn . ioeGetErrorString) proccessInput

proccessInput :: Options -> IO ()
proccessInput settOps =
    case optMainOption settOps of
       Translate -> (·) <$> progAsD <*> input >>= print
       Execute   -> flip catchIOError (putStrLn . ioeGetErrorString) $
                         evalProg <$> prog <*> input >>= pprint
    where -- Funciones para la ejecución.
          prog   :: IO Prog
          prog   = uncurry parseFileProg $ (optProgType &&& optProgFile) settOps
          input  :: IO Value
          input  = parseFileInput $ optInputFile settOps
          pprint :: Either EvalError Value -> IO ()
          pprint = flip printOutput (optOutMode settOps)
          -- Funciones para la traducción de un programa.
          progAsD :: IO Value
          progAsD = progToValue <$> prog
