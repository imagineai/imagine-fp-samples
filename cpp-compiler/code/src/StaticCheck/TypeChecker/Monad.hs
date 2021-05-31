module StaticCheck.TypeChecker.Monad where

import Syntax ( ClassName, Identifier, Type(..), IdDecl(..) )
import StaticCheck.TypeChecker.Error ( TCError(..) )

import Control.Monad.RWS   ( RWST, lift, when, unless, ask, put, get )
import Control.Applicative ((<$>))

import Data.Maybe (fromMaybe,fromJust)
import qualified Data.Map as M ( Map, empty, keys, member, lookup, insert )

data Type' = Basic Type
           | Array Type Integer
     deriving Show

type Context t = M.Map Identifier t

emptyCtx :: Context t
emptyCtx = M.empty

data ClassCtx = ClassCtx { ids   :: Context Type'
                         , mthds :: Context (Type,[Type])
                         }
     deriving Show
                    
emptyClassCtx :: ClassCtx
emptyClassCtx = ClassCtx { ids   = emptyCtx
                         , mthds = emptyCtx
                         }

type LocalIdCtx = Context Type'

type GlobalCtx = Context ClassCtx

data TCState = TCState { globalCtx :: GlobalCtx }
     deriving Show

emptyTCState :: TCState
emptyTCState = TCState { globalCtx = emptyCtx}
              
data LocalCtx = LocalCtx { idCtx    :: LocalIdCtx
                         , returnTy :: Type
                         , cname    :: ClassName
                         }

emptyLocalCtx :: LocalCtx
emptyLocalCtx = LocalCtx { idCtx    = emptyCtx 
                         , returnTy = VoidType
                         , cname    = ""
                         }

terror :: TCError -> TCheck a
terror = lift . Left

type TCheck = RWST LocalCtx () TCState (Either TCError)


getCNames :: TCheck [ClassName]
getCNames = M.keys . globalCtx <$> get


getGlobalCtx :: TCheck GlobalCtx
getGlobalCtx = globalCtx <$> get

-- PRE: c es un nombre de clase definida.
getClassCtx :: ClassName -> TCheck ClassCtx
getClassCtx c = fromMaybe (error "getClassCtx: Imposible. Clase no definida") . 
                M.lookup c <$> getGlobalCtx

-- 
-- getMthdCtx :: TCheck MthdContext
-- getMthdGCtx = mthdContext <$> get
-- 
getLocalIdCtx :: TCheck LocalIdCtx
getLocalIdCtx = idCtx <$> ask

getLocalReturnTy :: TCheck Type
getLocalReturnTy = returnTy <$> ask

getLocalCname :: TCheck ClassName
getLocalCname = cname <$> ask
-- 
-- 
-- checkIsClass :: Applicative a => (Bool -> a () -> a ()) -> 
--                 Identifier -> TCheck () -> TCheck ()
-- checkIsClass f i act = 
--     getCNames >>= cns ->
--     f (elem i cns) act
-- 
-- whenIsClass = checkIsClass when
-- 
-- unlessIsClass = checkIsClass unless

-- PRE: cn es un nombre de clase definida
checkIsGlobalDef :: (Bool -> TCheck () -> TCheck ()) -> 
                    ClassName -> Identifier -> TCheck () -> TCheck ()
checkIsGlobalDef f cn i act = 
    getClassCtx cn >>= \ctx -> f (M.member i (ids ctx)) act

whenIsGlobalDef :: ClassName -> Identifier -> TCheck () -> TCheck ()
whenIsGlobalDef = checkIsGlobalDef when

unlessIsGlobalDef :: ClassName -> Identifier -> TCheck () -> TCheck ()
unlessIsGlobalDef = checkIsGlobalDef unless

checkMethodIsDef :: (Bool -> TCheck () -> TCheck ()) -> 
                    ClassName -> Identifier -> TCheck () -> TCheck ()
checkMethodIsDef f cn i act =
    getClassCtx cn >>= \ctx -> f (M.member i (mthds ctx)) act
    
whenMethodIsDef :: ClassName -> Identifier -> TCheck () -> TCheck ()
whenMethodIsDef = checkMethodIsDef when

unlessMethodIsDef :: ClassName -> Identifier -> TCheck () -> TCheck ()
unlessMethodIsDef = checkMethodIsDef unless

--           

checkIsLocalDef :: (Bool -> TCheck () -> TCheck ()) -> 
                    Identifier -> TCheck () -> TCheck ()
checkIsLocalDef f i act = 
    getLocalIdCtx >>= \ctx -> f (M.member i ctx) act

whenIsLocalDef :: Identifier -> TCheck () -> TCheck ()
whenIsLocalDef = checkIsLocalDef when

unlessIsLocalDef :: Identifier -> TCheck () -> TCheck ()
unlessIsLocalDef = checkIsLocalDef unless

checkIsDefClass :: Type -> TCheck Type
checkIsDefClass t@(VType i) = 
    getCNames >>= \cns ->
    unless (i `elem` cns) (terror $ NotDefClass i) >>
    return t
checkIsDefClass t = terror $ TypeNotClass t


getTypeFromLocalCtx :: Identifier -> TCheck (Maybe Type')
getTypeFromLocalCtx i = M.lookup i <$> getLocalIdCtx 
    
getTypeFromGlobalCtx :: ClassName -> Identifier -> TCheck (Maybe Type')
getTypeFromGlobalCtx cn i = M.lookup i . ids <$> getClassCtx cn

-- PRE: i está definido en el local o en el global
getIdType :: Identifier -> TCheck Type'
getIdType i = 
    getLocalCname >>= \cn ->
    getTypeFromLocalCtx i >>=
    maybe (fromJust <$> getTypeFromGlobalCtx cn i) return
          
getTypeFromMthdCtx :: ClassName -> Identifier -> TCheck (Maybe (Type,[Type]))
getTypeFromMthdCtx cn i = M.lookup i . mthds <$> getClassCtx cn

-- PRE: m esta definido como metodo
getMthdType :: Identifier -> TCheck (Type,[Type])
getMthdType m = getLocalCname >>= \cn -> 
                fromJust <$> getTypeFromMthdCtx cn m


-- -- Pre: loc está definida
-- -- getDef :: Location -> TCheck Type'
-- -- getDef loc = 
--     
-- 
-- Agrega un nombre de clase.
-- PRE: El nombre no se encuentra en la lista
addClassName :: ClassName -> TCheck ()
addClassName c = get >>= \st ->
                 getGlobalCtx >>= \ctx ->
                 put (st { globalCtx = addCtx c emptyClassCtx ctx })
-- 
-- PRE: c es el nombre de una clase definida.       
addIdToClassCtx :: ClassName -> Identifier -> Type' -> TCheck ()
addIdToClassCtx c i ty' =
    get >>= \st ->
    getGlobalCtx >>= \gctx ->
    getClassCtx c >>= \cctx ->
    let idctx = addCtx i ty' (ids cctx)
        cctx' = cctx { ids = idctx } in
        put (st { globalCtx = addCtx c cctx' gctx })
        
-- PRE: c es el nombre de una clase definida.
addMthdToClassCtx :: ClassName -> Identifier -> Type -> [Type] -> TCheck ()
addMthdToClassCtx c i rTy tys =
    get >>= \st ->
    getGlobalCtx >>= \gctx ->
    getClassCtx c >>= \cctx ->
    let mthdctx = addCtx i (rTy,tys) (mthds cctx)
        cctx' = cctx { mthds = mthdctx } in
        put (st { globalCtx = addCtx c cctx' gctx })

-- -- PRE: el identificador idecl no se encuentra definido
-- addLocToGCtx :: Location -> Type' -> TCheck ()
-- addLocToGCtx loc ty' = 
--                 do
--                     st <- get
--                     let gctx       = globalCtx st
--                     put (st { globalCtx = (addCtx loc ty' *** id) gctx})
-- 
--                     
-- addMthdToGlobalCtx :: Location -> Maybe Type -> [Type] -> TCheck ()
-- addMthdToGlobalCtx loc mTy argsTy = 
--                 do
--                     st <- get
--                     let gctx = globalCtx st
--                     put (st { globalCtx = (id *** addCtx loc (mTy,argsTy)) gctx})
--                     
--                     
addToLocalRTyCtx :: Type -> LocalCtx -> LocalCtx
addToLocalRTyCtx rTy lctx = lctx { returnTy = rTy }

addToLocalIdCtx :: Identifier -> Type' -> LocalCtx -> LocalCtx
addToLocalIdCtx i ty' lctx = lctx { idCtx = addCtx i ty' (idCtx lctx) }

addToLocalClassName :: ClassName -> LocalCtx -> LocalCtx
addToLocalClassName cn lctx = lctx { cname = cn }

addCtx :: Identifier -> t -> Context t -> Context t
addCtx = M.insert

checkDefType :: Type -> TCheck ()
checkDefType (VType tyi) = getCNames >>= \cns ->
                           if elem tyi cns
                           then return ()
                           else terror $ NotDefClass tyi
checkDefType _ = return ()

-- A partir de una declaracion de variable y un Type, construye el Type' correspondiente
mkType' :: IdDecl -> Type -> Type'
mkType' (Id _) ty       = Basic ty
mkType' (Arr _ size) ty = Array ty size

typeFromType' :: Type' -> Type
typeFromType' (Basic ty) = ty
typeFromType' (Array ty _) = ty


                    
