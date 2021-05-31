module InterCode.Monad where

import Syntax              ( Identifier, Type )
import InterCode.InterCode ( Register, Label(..), Size, unwrapLabel )

import Control.Arrow       ( (***) )
import Control.Monad.RWS   ( RWS, ask, modify, put, get )
import Control.Applicative ( (<$>) )

import Data.Maybe              ( fromJust )
import qualified Data.Map as M ( Map, empty, insert, union, lookup )

type RegsAssign = M.Map Identifier Register

data ICReader = ICReader { regsAssign    :: RegsAssign
                         , labelBreak    :: Maybe Label
                         , labelContinue :: Maybe Label
                         }
    deriving Show

data ICState = ICState { labelMax  :: Label
                       , externIds :: [Identifier]
                       , regMax    :: Register
                       , regStore  :: Maybe (Register,[(Type,Size)])
                       }
    deriving Show

type IC a = RWS ICReader () ICState a 

emptyICR :: ICReader
emptyICR = ICReader { regsAssign    = M.empty
                    , labelBreak    = Nothing
                    , labelContinue = Nothing
                    }

emptyICS :: ICState
emptyICS = ICState { labelMax  = L ("L",1)
                   , externIds = []
                   , regMax    = 0
                   , regStore  = Nothing
                   }

askReader :: IC ICReader
askReader = ask >>= return

askRegsAssign :: IC RegsAssign
askRegsAssign = ask >>= return . regsAssign

-- PRE: El label ya fue "seteado" con anterioridad.
askBreakLabel :: IC Label
askBreakLabel = ask >>= return . fromJust . labelBreak

-- PRE: El label ya fue "seteado" con anterioridad.
askContinueLabel :: IC Label
askContinueLabel = ask >>= return . fromJust . labelContinue

addExternId :: Identifier -> IC ()
addExternId i = get >>= \st ->
                put (st { externIds = i : externIds st })

getExternIds :: IC [Identifier]
getExternIds = externIds <$> get

isExternId :: Identifier -> IC Bool
isExternId i = elem i <$> getExternIds

setInitialRegMax :: Int -> IC ()
setInitialRegMax i = modify (\st -> st { regMax = i })

getRegMax :: IC Register
getRegMax = get >>= return . regMax

updateRegMax :: IC ()
updateRegMax = get >>= \st -> 
               getRegMax >>= \r ->
               put (st {regMax = r+1})

newReg :: IC Register
newReg = getRegMax >>= \r -> updateRegMax >> return r

getRegStore :: IC (Maybe (Register,[(Type,Size)]))
getRegStore = get >>= return . regStore

addRegStore :: (Type,Size) -> IC Register
addRegStore ts = getRegStore >>= \rs ->
                 newReg >>= \r ->
                 get >>= \st -> 
                 case rs of
                    Nothing       -> put (st {regStore = Just (r,[ts])})
                    Just (ri,tss) -> put (st {regStore = Just (ri,(tss++[ts]))})
                 >> return r

resetRegStore :: IC ()
resetRegStore = get >>= \st -> put (st {regStore = Nothing})

getLabelMax :: IC Label
getLabelMax = get >>= return . labelMax

getLabelMaxWithString :: String -> IC Label
getLabelMaxWithString str = getLabelMax >>=
                            return . L . (***) (const str) id . unwrapLabel

updateLabelMax :: IC ()
updateLabelMax = get >>= \st -> 
                 getLabelMax >>= \(L l) ->
                 put (st {labelMax = L $ id *** (+1) $ l})

addBreakLabel :: Label -> ICReader -> ICReader
addBreakLabel l icr = icr { labelBreak = Just l }

addContinueLabel :: Label -> ICReader -> ICReader
addContinueLabel l icr = icr { labelContinue = Just l }

addRegsAssign :: Identifier -> Register -> ICReader -> ICReader
addRegsAssign i r icr = let ras = regsAssign icr
                        in icr {regsAssign = M.insert i r ras}

unionRegsAssign :: RegsAssign -> ICReader -> ICReader
unionRegsAssign ras icr = let ras' = regsAssign icr
                          in icr {regsAssign = primitiveUnionRas ras ras'}

updateRegsAssign :: RegsAssign -> ICReader -> ICReader
updateRegsAssign ras icr = icr {regsAssign = ras}

getRegister :: Identifier -> IC Register
getRegister i = askRegsAssign >>=
                return . primitiveGetRegRas i

primitiveUnionRas :: RegsAssign -> RegsAssign -> RegsAssign
primitiveUnionRas = M.union

-- PRE: El identificador existe en ras :: RegsAssign
primitiveGetRegRas :: Identifier -> RegsAssign -> Register
primitiveGetRegRas i = fromJust . M.lookup i
