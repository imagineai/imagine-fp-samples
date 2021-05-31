module Main.IWhile.CmdHandler where

import System.Console.Haskeline
import Data.Char ( isSpace )

import Main.IWhile.Monad
import Main.IWhile.Cmd

promptMsg :: IStateM String
promptMsg = do
              p <- getProg
              d <- getData
              return ("[" ++ pstr p ++ "," ++ dstr d ++ "] > ")
    where pstr p = case p of
                     Nothing        -> "--"
                     Just lp -> lProgName lp
          dstr d = case d of
                     Nothing        -> "--"
                     Just (_,dname) -> dname

loopMain :: IStateM ()
loopMain = do
        prompt <- promptMsg
        minput <- getInputLine prompt
        case minput of
            Nothing     -> return ()
            Just str    -> catch (mainCases (splitInp str)) catchException

catchException :: SomeException -> IStateM ()
catchException e = showMsg (show e) >> loopMain

mainCases :: [String] -> IStateM ()
mainCases []         = loopMain
mainCases ("quit":_) = return ()
mainCases (cmd:opts) = choiceCmd cmd opts
 
execCmd :: Cmd -> [String] -> IStateM ()
execCmd cmd uargs 
      | length (args cmd) /= length uargs = showCmdUsage cmd >> loopMain
      | check (args cmd) uargs           = action cmd uargs >> loopMain
      | otherwise                        = showCmdUsage cmd >> loopMain
    where check :: [Arg] -> [String] -> Bool
          check [] []        = True
          check (a:_) (ua:_) = case a of
                                   Choice opts -> ua `elem` opts
                                   Param _     -> True
          check _ _ = error "Imposible: check-execCmd"

cmdNotValid :: IStateM ()
cmdNotValid = showMsg $ unlines [ ""
                                , "Comando no válido. Ingrese help para ayuda."
                                ]

showCmdUsage :: Cmd -> IStateM ()
showCmdUsage cmd = showMsg $ unlines [ "\nUso: "
                                     , '\t' : show cmd
                                     ]

choiceCmd :: String -> [String] -> IStateM ()
choiceCmd cname opts = fchoice cmdList
    where fchoice :: [Cmd] -> IStateM ()
          fchoice [] = cmdNotValid >> loopMain
          fchoice (cmd:rest) = if cname == cmdName cmd
                                 then execCmd cmd opts
                                 else fchoice rest

initShow :: IStateM ()
initShow = showMsg $
    unlines [ ""
            , "\t\t--- WHILE intérprete, versión 0.1 ---"
            , "\t\t          (help para ayuda)"
            ]

            {-
            [
            , ""
            , "'The name of the song is called \"Haddocks’ Eyes.\"'"
            , ""
            , "'Oh, that's the name of the song, is it?' Alice said, trying to feel interested."
            , ""
            , "'No, you don't understand,' the Knight said, looking a little vexed."++
              "'That's what the name is called. The name really is \"The Aged Aged Man.\"'"
            , ""
            , "'Then I ought to have said \"That's what the song is called\"?' Alice corrected herself."
            , ""
            , "'No, you oughtn't: that's quite another thing! The song is called \"Ways and Means\":" ++ 
              "but that's only what it's called, you know!'"
            , ""
            , "'Well, what is the song, then?' said Alice, who was by this time completely bewildered."
            , ""
            , "'I was coming to that,' the Knight said. 'The song really is \"A-sitting On A Gate\":"++
              "and the tune's my own invention.'"
            , ""
            ]-}

-- Auxiliar
splitInp :: String -> [String]
splitInp = filter (/="") . splitInp'

splitInp' :: String -> [String]
splitInp' "" = []
splitInp' str@(c:s) | c == '\"' = let (quoted,restQ) = break (=='\"') s
                                 in quoted : splitInp' (drop 1 restQ)
                   | otherwise = fstStr : splitInp' rest
    where fstStr = takeWhile (not . isSpace) str
          rest = drop (length fstStr + 1) str
