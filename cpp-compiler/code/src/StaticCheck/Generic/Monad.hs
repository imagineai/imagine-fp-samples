module StaticCheck.Generic.Monad where

import Syntax ( Identifier )

import Control.Monad.RWS ( RWS, ask, get, put )

data GState = GState 
              { missingMain        :: Bool
              , incorrectProtMain  :: Bool
              , incorrectArraySize :: [Identifier]
              , misplacedBreak     :: [Identifier]
              , misplacedCont      :: [Identifier]
              , missingReturn      :: [Identifier]
              }
    deriving Show

data GReader = GReader
               { inCicle       :: Bool
               , inNonVoidFunc :: Bool
               }

type GenericCheck = RWS GReader () GState

initGReader :: GReader
initGReader = GReader 
              { inCicle       = False
              , inNonVoidFunc = False
              }

initGState :: GState
initGState = GState
             { missingMain        = True
             , incorrectProtMain  = False
             , incorrectArraySize = []
             , misplacedBreak     = []
             , misplacedCont      = []
             , missingReturn      = []
             }

askInNonVoidFunc :: GenericCheck Bool
askInNonVoidFunc = ask >>= return . inNonVoidFunc

setInNonVoidFunc :: GReader -> GReader
setInNonVoidFunc gr = gr {inNonVoidFunc = True}

askInCicle :: GenericCheck Bool
askInCicle = ask >>= return . inCicle

setInCicle :: GReader -> GReader
setInCicle gr = gr {inCicle = True}

findedMain :: GenericCheck ()
findedMain = get >>= \st -> put (st {missingMain = False})

setIncorrectProtMain :: GenericCheck ()
setIncorrectProtMain = get >>= \st -> put (st {incorrectProtMain = True})

addMissingReturn :: Identifier -> GenericCheck ()
addMissingReturn i = get >>= \st ->
                     let asl = missingReturn st
                     in put (st {missingReturn = i:asl})

addMisplacedBreak :: Identifier -> GenericCheck ()
addMisplacedBreak i = get >>= \st ->
                      let asl = misplacedBreak st
                      in put (st {misplacedBreak = i:asl})

addMisplacedCont :: Identifier -> GenericCheck ()
addMisplacedCont i = get >>= \st ->
                     let asl = misplacedCont st
                     in put (st {misplacedCont = i:asl})

addIncorrectArraySize :: Identifier -> GenericCheck ()
addIncorrectArraySize i = get >>= \st ->
                          let asl = incorrectArraySize st
                          in put (st {incorrectArraySize = i:asl})
