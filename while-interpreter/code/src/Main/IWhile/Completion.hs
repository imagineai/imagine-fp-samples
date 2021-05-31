module Main.IWhile.Completion where

import Data.List ( find, isPrefixOf )
import System.Console.Haskeline ( Completion, CompletionFunc
                                , simpleCompletion
                                , completeWordWithPrev
                                , listFiles
                                )

import Main.IWhile.Cmd   ( cmdNameList , Cmd (..) , cmdList , Arg (..) )
import Main.IWhile.Monad ( IStateT )

simpleComplete :: String -> [String] -> [Completion]
simpleComplete str = map simpleCompletion . filter (isPrefixOf str)

searchCmd :: String -> [Completion]
searchCmd = flip simpleComplete cmdNameList

getCmd :: String -> Maybe Cmd
getCmd cname = find ((cname ==) . cmdName) cmdList

completeArg :: Cmd -> String -> IStateT [Completion]
completeArg cmd str =
    case (args cmd, head $ args cmd) of
        ([],_)           -> return []
        (_:_, Choice cs) -> return $ simpleComplete str cs
        _                -> listFiles str

-- Autocompleta los argumentos de un comando. Implementado
-- sólo para un argumento.
completeArgs :: String -> String -> IStateT [Completion]
completeArgs cmd arg = maybe (return []) (`completeArg` arg) (getCmd cmd)

completeCmd :: String -> String -> IStateT [Completion]
completeCmd []  = return . searchCmd
-- obtenemos el comando completo tirando el último
-- caracter, el cual es un espacio.
completeCmd str = completeArgs (init (reverse str))

-- Autocompleta un cómando.
completeCmds :: CompletionFunc IStateT
completeCmds = completeWordWithPrev Nothing " \t" completeCmd
