module Machine.Monad where

import Syntax ( Type(..),Literal(..) )
import Machine.Code  ( Size(..), Code, Location(..), Instruction(..), Value(..)
                     , Register(..), RegName(..), MemAddress(..), Mem(..)
                     , Label
                     , selfAddr, maToLoc
                     , r10
                     )
import qualified InterCode as IC ( Operand(..), Register, Size)

import Control.Arrow       ( (***), (&&&) )
import Control.Monad.State ( State, get, modify )
import Control.Applicative ( (<$>) )

import Data.Maybe ( fromJust )
import qualified Data.Map as M ( Map, empty, insert, union, lookup )

type MemAssign = M.Map IC.Register (MemAddress,Type)

data Header = Header { labelN       :: Int
                     , stringLabels :: [(Label,String)]
                     }
    deriving Show

data MState = MState { header    :: Header
                     , storeG    :: [(Type,IC.Size)]
                     , memAssign :: MemAssign
                     }
    deriving Show

type Machine = State MState

emptyHeader :: Header
emptyHeader= Header { labelN = 0
                    , stringLabels = []
                    }

emptyMState :: MState
emptyMState = MState { header = emptyHeader
                     , storeG = []
                     , memAssign = emptyMAssign
                     }

emptyMAssign :: MemAssign
emptyMAssign = M.empty

strLabelPrefix :: Label
strLabelPrefix = ".LC"

setStoreG :: [(Type,IC.Size)] -> Machine ()
setStoreG sg = modify (\ms -> ms { storeG = sg })

getStoreG :: Machine [(Type,IC.Size)]
getStoreG = storeG <$> get

isGlobal :: IC.Register -> Machine Bool
isGlobal reg = getStoreG >>= \sg ->
               return $ reg < length sg

getGlobalIndex :: IC.Register -> Machine Integer
-- Tiramos el primero porque el selfAddr ya apunto a este mismo. No
-- hace falta corrimiento.
getGlobalIndex reg = foldl f 0 . take reg . drop 1 <$> getStoreG
    where
        f :: Integer -> (Type,IC.Size) -> Integer
        f res (ty,size) = res - (icTypeToMSize ty) * size

getGlobalIndexTy :: IC.Register -> Machine Type
getGlobalIndexTy reg = fst . flip (!!) reg <$> getStoreG

addStringToHeader :: String -> Machine Label
addStringToHeader str = getNewStringLabel >>= \l ->
                        addStrToHeader l >>= \h ->
                        modify (upd h) >>
                        return l
    where upd :: Header -> MState -> MState
          upd h mst = mst { header = h }
          addStrToHeader :: Label -> Machine Header
          addStrToHeader l = getHeader >>= \h ->
                             getStringLabels >>= \sls ->
                             return (h { stringLabels = (l,str):sls })

getStringLabels :: Machine [(Label,String)]
getStringLabels = stringLabels <$> getHeader

getLabelN :: Machine Int
getLabelN = labelN <$> getHeader

getNewStringLabel :: Machine Label
getNewStringLabel = labelN <$> getHeader >>= \i ->
                    updateStringLabel >>
                    return (strLabelPrefix ++ show i)

updateStringLabel :: Machine ()
updateStringLabel = (+1) <$> getLabelN >>= \n ->
                    (\h -> h {labelN = n}) <$> getHeader >>= \h ->
                    modify (\mst -> mst { header = h })

getHeader :: Machine Header
getHeader = header <$> get

getMemAssign :: Machine MemAssign
getMemAssign = memAssign <$> get

addMAssign :: IC.Register -> (MemAddress,Type) -> MemAssign -> MemAssign
addMAssign = M.insert

unionMemAssign :: MemAssign -> Machine ()
unionMemAssign ma = 
               modify (\mst -> mst { memAssign = M.union ma (memAssign mst) })

lookupMAss :: IC.Register -> Machine ([Instruction],MemAddress)
lookupMAss r = isGlobal r >>= \isG ->
               if not isG
               then getMemAssign >>= 
                    return . (const [] &&& id) . fst . fromJust . M.lookup r
               else getGlobalIndex r >>= \offset ->
                    let maddr  = MAddr offset (R Quad R10)
                        movg   = [ MOV Quad (Loc $ maToLoc selfAddr) r10 ]
                    in return (movg, maddr)

lookupType :: IC.Register -> Machine Type
lookupType r = isGlobal r >>= \isG ->
               if not isG
               then getMemAssign >>= return . snd . fromJust . M.lookup r
               else getGlobalIndexTy r

stickMLabel :: Label -> Code -> Code
stickMLabel _ [] = []
stickMLabel l ((_,c):cs) = (l,c):cs

icOpToValue :: IC.Operand -> Machine ([Instruction],Value)
icOpToValue (IC.C (IntL i)) = return ([],C i)
icOpToValue (IC.C (BoolL b)) = return $ if b then ([],C 1) else ([],C 0)
icOpToValue (IC.C (StringL s)) =  (const [] &&& Str) <$> addStringToHeader s
icOpToValue (IC.C _)  = error "solo implementadas constantes enteras y bool"
icOpToValue (IC.R reg) = lookupMAss reg >>= return . (id *** Loc . MA . MAdd)

icOpToType :: IC.Operand -> Machine Type
icOpToType (IC.C (IntL _)) = return IntType
icOpToType (IC.C (FloatL _)) = return FloatType
icOpToType (IC.C (BoolL _)) = return BoolType
icOpToType (IC.C (StringL _)) = return StringType
icOpToType (IC.R r) = lookupType r

icTypeToMSize :: Type -> Integer
icTypeToMSize BoolType   = 1
icTypeToMSize IntType    = 4
icTypeToMSize StringType = 0
icTypeToMSize _ = error "tipo de dato no implementado en Machine"

icRegToLoc :: IC.Register -> Machine ([Instruction],Location)
icRegToLoc r = lookupMAss r >>= return . (id *** MA . MAdd)
