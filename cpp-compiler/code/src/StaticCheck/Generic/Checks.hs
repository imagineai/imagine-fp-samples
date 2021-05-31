{- 

# Este módulo sirve para realizar los siguientes chequeos estaticos:

- Existe método "main".
- El método "main" tiene cantidad de parametros nula.
- Declaración de variable de tipo arreglo, tiene tamaño mayor a cero.
- Las sentencias "break" y "continue" solo aparecen en el cuerpo de un ciclo.
- Existe el statement "return" en un metodo cuyo tipo de retorno no es void.

-}
module StaticCheck.Generic.Checks
       ( genericChecksProgram, checkErrors )
       where

import Syntax ( Program
              , ClassDecl, ClassDecl'(..)
              , Statement, Statement'(..)
              , MethodDecl, MethodDecl'(..)
              , Body, Body'(..)
              , Block'(..), FieldDecl(..), IdDecl(..), ParamDecl(..), Identifier
              )

import StaticCheck.Generic.Error ( GenericErrors, GenericError(..) )
import StaticCheck.Generic.Monad ( GenericCheck, findedMain
                                 , addIncorrectArraySize, incorrectArraySize
                                 , setIncorrectProtMain, incorrectProtMain
                                 , addMisplacedCont, misplacedCont
                                 , addMisplacedBreak, misplacedBreak
                                 , askInCicle, setInCicle
                                 , addMissingReturn, missingReturn
                                 , askInNonVoidFunc, setInNonVoidFunc
                                 , GState, missingMain
                                 )

import Control.Monad       ( forM, forM_, when, unless )
import Control.Monad.RWS   ( local )
import Control.Applicative ( (<$>) )

checkErrors :: GState -> GenericErrors
checkErrors gs =  
      grabError missingMain                   (const MissingMethodMain)
   ++ grabError incorrectProtMain             (const IncorrectPrototipeMain)
   ++ grabError (existError . misplacedBreak) (MisplacedBreak . misplacedBreak)
   ++ grabError (existError . misplacedCont)  (MisplacedContinue . misplacedCont)
   ++ grabError (existError . missingReturn)  (MissingReturn . missingReturn)
   ++ grabError (existError . incorrectArraySize) 
                 (IncorrectArraySize . incorrectArraySize)
    where 
        grabError :: (GState -> Bool) -> (GState -> GenericError) -> 
                     [GenericError]
        grabError getErr ge | getErr gs = [ge gs]
        grabError _ _       | otherwise = []
        existError :: [a] -> Bool
        existError l = length l > 0

genericChecksProgram :: Program -> GenericCheck ()
genericChecksProgram = flip forM_ genericChecksClass

genericChecksClass :: ClassDecl -> GenericCheck ()
genericChecksClass (ClassDecl _ fdecls mdecls) = 
                   genericChecksFieldDecls fdecls >>
                   genericChecksMethodDecls mdecls

genericChecksFieldDecls :: [FieldDecl] -> GenericCheck ()
genericChecksFieldDecls = flip forM_ genericChecksFD

genericChecksMethodDecls :: [MethodDecl] -> GenericCheck ()
genericChecksMethodDecls = flip forM_ genericChecksMD

genericChecksMD :: MethodDecl -> GenericCheck ()
genericChecksMD (Fun _ i params body) = checkMainMethod i params >>
                                         local setInNonVoidFunc
                                               (genericCheckBody i body)
genericChecksMD (Proc i params body) = checkMainMethod i params  >>
                                       genericCheckBody i body

genericCheckBody :: Identifier -> Body -> GenericCheck ()
genericCheckBody i (Local (Block fds stmts)) =
                   genericChecksFieldDecls fds >>
                   genericChecksStatements i stmts >>= 
                   existRet
    where existRet :: Bool -> GenericCheck ()
          existRet True  = return ()
          existRet False = askInNonVoidFunc >>= flip when (addMissingReturn i)
genericCheckBody _ _ = return ()

genericChecksStatements :: Identifier -> [Statement] -> GenericCheck Bool
genericChecksStatements i stmts = or <$> forM stmts (genericChecksSTMT i)
                                
genericChecksSTMT :: Identifier -> Statement -> GenericCheck Bool
genericChecksSTMT i (For _ _ _ stmt) = local setInCicle
                                       (genericChecksSTMT i stmt) >>= return
genericChecksSTMT i (While _ stmt)   = local setInCicle
                                       (genericChecksSTMT i stmt) >>= return
genericChecksSTMT i Break            = askInCicle >>= 
                                       flip unless (addMisplacedBreak i) >> 
                                       return False
genericChecksSTMT i Continue         = askInCicle >>= 
                                       flip unless (addMisplacedCont i) >>
                                       return False
genericChecksSTMT _ (Return _)       = return True
genericChecksSTMT _ _                = return False

genericChecksFD :: FieldDecl -> GenericCheck ()
genericChecksFD (FieldDecl _ ids) = forM_ ids checkArraySize

checkMainMethod :: Identifier -> [ParamDecl] -> GenericCheck ()
checkMainMethod i params = case (i == "main", length params == 0) of
                                (True,True)  -> findedMain >> return ()
                                (False,_)    -> return ()
                                (True,False) -> findedMain >>
                                                setIncorrectProtMain

checkArraySize :: IdDecl -> GenericCheck ()
checkArraySize (Arr i size) = if size > 0 then return ()
                              else addIncorrectArraySize i
checkArraySize _ = return ()
