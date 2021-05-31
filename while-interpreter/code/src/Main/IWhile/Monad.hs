module Main.IWhile.Monad where

import System.FilePath.Posix      ( takeBaseName )
import System.Console.Haskeline   ( InputT, outputStrLn )
import Control.Monad.State.Strict ( StateT, lift, get, modify )
import Control.Applicative        ( (<$>) )

import Prog  ( Prog )
import Value ( Value(Dot) )

type ProgName  = String
type ValueName = String

data LoadedProg = LoadedProg { lProg     :: Prog
                             , lProgName :: ProgName
                             , fpProg    :: FilePath
                             }

data IState = IState { prog  :: Maybe LoadedProg
                     , pdata :: Maybe (Value,ValueName)
                     }

initState :: IState
initState = IState { prog  = Nothing
                   , pdata = Nothing
                   }

type IStateT = StateT IState IO

type IStateM = InputT IStateT

showError :: String -> IStateM ()
showError msg = outputStrLn (msg ++ "\n")

showMsg :: String -> IStateM ()
showMsg msg = outputStrLn (msg ++ "\n")

getProg :: IStateM (Maybe LoadedProg)
getProg = prog <$> lift get

getData :: IStateM (Maybe (Value,ValueName))
getData = pdata <$> lift get

updateProg :: Prog -> FilePath -> IStateM ()
updateProg p fp = lift $ modify 
                  (\st -> st {prog = Just $ LoadedProg p pname fp})
    where pname :: ProgName
          pname = takeBaseName fp

updateData :: Value -> ValueName -> IStateM ()
updateData d name = lift $ modify (\st -> st {pdata = Just (d,name)})

appendData :: Value -> ValueName -> IStateM ()
appendData d name = 
    whenData (\(v,n) ->
    updateData (Dot v d) (n ++ "." ++ name))

io :: IO a -> IStateM a
io = lift . lift

-- Acciones que requieren que tengamos
-- cargado un programa
whenProg :: (LoadedProg -> IStateM ()) -> IStateM ()
whenProg act = getProg >>= maybe (showError "No hay un programa cargado.") act

whenData :: ((Value,ValueName) -> IStateM ()) -> IStateM ()
whenData act = getData >>= maybe (showError "No hay un dato cargado.") act
