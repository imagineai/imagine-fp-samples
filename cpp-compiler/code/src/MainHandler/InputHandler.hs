module MainHandler.InputHandler ( proccessInputFile ) where

import MainHandler.ArgsHandler ( Options(..), Phase(..) )
import MainHandler.Exceptions  ( MainExceptions(..) )

import Parser      ( parseFromString )
import Syntax      ( Program, pprintProgram )
import Machine     ( generateAssembly, pprintCode )
import InterCode   ( InterCode, generateInterCode, pprintInterCode )
import StaticCheck ( TypedProgram, pprintTyProgram, genericChecks
                   , typecheckProgram
                   )

import Control.Monad     ( void )
import Control.Arrow     ( (&&&) )
import System.Process    ( callCommand )
import System.FilePath   ( dropExtension, (<.>), (-<.>) )
import Control.Exception ( throwIO, catch )

import Data.Maybe ( fromJust, fromMaybe )

mainExcHandlers :: MainExceptions -> IO ()
mainExcHandlers (ParserE pe)      = printException "Parse Error:" pe
mainExcHandlers (GenericE ger)    = printException "Static Check Error:" ger
mainExcHandlers (TypeCheckE tcer) = printException "Type Checker Error:" tcer

printException :: Show err => String -> err -> IO ()
printException title err = putStrLn $ unlines 
                           [ ""
                           , title
                           , ""
                           , show err
                           , ""
                           ]

proccessInputFile :: Options -> IO ()
proccessInputFile = flip catch mainExcHandlers .
                    proccessIF . (fromJust . optInName &&& id)

proccessIF :: (FilePath,Options) -> IO ()
proccessIF (fp,opts) = do
        let phase = optTarget opts
        
        code <- readFile fp
        
        case phase of
            Parse       -> void $ parse code
            StaticCheck -> void $ parse code >>= staticCheck
            CodInter    -> void $ parse code >>= staticCheck >>= interCode
            Assembly    -> parse code >>= staticCheck >>= interCode >>= assembly
            Executable  -> parse code >>= staticCheck >>= interCode >>=
                           assembly >> executable
            _           -> error "Imposible: la fase por default es Executable"
    where
        parse :: String -> IO Program
        parse code = case parseFromString code of
                          Right p -> writeOutput "sint" fp
                                                 (show $ pprintProgram p) >>
                                     return p
                          Left pe -> throwIO $ ParserE pe
        
        interCode :: TypedProgram -> IO InterCode
        interCode tp = let ic = generateInterCode tp
                       in writeOutput "ic" fp (pprintInterCode ic) >>
                          return ic

        assembly :: InterCode -> IO ()
        assembly ic = let ass = generateAssembly ic
                      in writeOutput "s" fp (uncurry pprintCode ass)
        
        executable :: IO ()
        executable = let asmFile = fp -<.> ".s"
                         fname = fromMaybe (dropExtension fp) $ optOutName opts
                     in callCommand $ unwords [ asmCompiler
                                              , "-o"
                                              , fname
                                              , asmFile
                                              , asmCompilerOptions
                                              ]
        
        staticCheck :: Program -> IO TypedProgram
        staticCheck p = genericCheck p >> typeCheck p >>= \tp ->
                        writeOutput "tysint" fp (show $ pprintTyProgram tp) >>
                        return tp

        genericCheck :: Program -> IO ()
        genericCheck p = case genericChecks p of
                              [] -> return ()
                              ge -> throwIO $ GenericE ge

        typeCheck :: Program -> IO TypedProgram
        typeCheck p = case typecheckProgram p of
                           Right tp -> return tp
                           Left tcerr -> throwIO $ TypeCheckE tcerr

writeOutput :: String -> FilePath -> String -> IO ()
writeOutput ext fp str = do
            let fname = dropExtension fp
            writeFile (fname <.> ext) str

asmCompiler :: String
asmCompiler = "gcc"

asmCompilerOptions :: String
asmCompilerOptions = "-no-pie"
