module Main where

import MainHandler.ArgsHandler  ( checkArgs )
import MainHandler.InputHandler ( proccessInputFile )

import System.Environment ( getArgs )
import System.IO.Error    ( ioeGetErrorString )

main :: IO ()
main = do
   args <- getArgs

   fpOpts <- checkArgs args
   
   either (putStrLn . ioeGetErrorString) proccessInputFile fpOpts
