module Main where

import System.Environment

import Lambda
import Parser
import Type
import Examples

main :: IO ()
main = do
        args <- getArgs
        if length args == 0 
        then displayHelp
        else case args of
                ["--help"]         -> displayHelp
                ["--showExamples"] -> displayExamples
                ["--getType",term] -> displayTerm term
                _                  -> displayHelp

displayExamples :: IO ()
displayExamples = do
               putStrLn $ unlines $ reverse $ snd $ foldl p (0,[]) examples
    where
        p :: (Int,[String]) -> Term -> (Int,[String])
        p (i,ts) t = ( i+1
                     , displayTermAndType (Just i) t Nothing (getType t) : ts
                     )

displayTerm :: String -> IO ()
displayTerm term = do
    case parserTerm term of
        (t,[]) -> putStrLn $ displayTermAndType Nothing t Nothing $ getType t
        (t,es) -> putStrLn $ displayTermAndType Nothing t (Just es) $ getType t

displayTermAndType :: Maybe Int -> Term -> Maybe ParseError -> Type -> String
displayTermAndType mi t merr ty = unlines 
            [ maybe "" (\i -> "############### " ++ show i ++ ":\n") mi
            , "Term: "
            , show t
            , maybe "" (\err -> "\nCorrection:\n" ++ showErr err) merr
            , "Type: "
            , show ty
            ]
    where
        showErr :: ParseError -> String
        showErr = unlines . map show 

displayHelp :: IO ()
displayHelp = putStrLn $ unlines 
    [ ""
    , "Usage: infer OPTION ..."
    , ""
    , "Option:"
    , "    --help                 Display this info."
    , "    --showExamples         Display predefined examples infers his types."
    , "    --getType \"Term\"     Parse and infer type of Term."
    , ""
    , "Var ::= Strings"
    , ""
    , "Term ::= Var"
    , "      | \\Var . Term"
    , "      | Term @ Term"
    ]
