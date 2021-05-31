module Main where

import System.Console.Haskeline   ( runInputT, Settings(..) )
import Control.Monad.State.Strict ( void, runStateT, StateT )
import Control.Applicative        ( (<$>) )
import System.FilePath            ( (</>) )
import System.Directory           ( getHomeDirectory )

import Main.IWhile.Monad      ( IState, IStateT, initState )
import Main.IWhile.CmdHandler ( initShow, loopMain )
import Main.IWhile.Completion ( completeCmds )

historyFilePath :: IO FilePath
historyFilePath = (</> ".iwhile_history") <$> getHomeDirectory

iwhileSetting :: FilePath -> Settings (StateT IState IO)
iwhileSetting hfp = Settings { complete       = completeCmds
                             , historyFile    = Just hfp
                             , autoAddHistory = True
                             }

main :: IO ()
main = historyFilePath >>= \hfp ->
       void $ runStateT (runInput hfp) initState
    where runInput :: FilePath -> IStateT ()
          runInput hfp = runInputT (iwhileSetting hfp) (initShow >> loopMain)
