{- Módulo para definir la traducción del comando rewrite en comandos 
básicos, de acuerdo a la sección 2.3.1 -}
module ExtendedLanguage.Rewrite ( compileRewrite
                                , CompileRW
                                , CompError
                                , initStateRW) where

import ExtendedLanguage.ExtLanguage
import Expr
import Value

import qualified Data.Map as M
import Control.Arrow
import Control.Applicative
import Control.Monad.State
import Data.Maybe ( fromMaybe )
                       
-- Error de compilación
type CompError = String
                       
{- Estado para llevar la asignacion de variables en los patrones
y una función para construir los "if" anidados -}
data StateRW = StateRW { vmap :: M.Map Var Expr
                       , partIf :: ExtComm -> ExtComm
                       }

initStateRW :: StateRW            
initStateRW = StateRW M.empty id

resetState :: StateT StateRW (Either CompError) ()
resetState = put initStateRW
     
{- Mónada de estado -}
type CompileRW a = StateT StateRW (Either CompError) a

compileRewrite :: [Var] -> [Rule] -> CompileRW ExtComm
compileRewrite vs rs = foldr1 ESeq <$> mapM (compileRule vs >=> \ec ->
                                             resetState >> return ec) rs

compileRule :: [Var] -> Rule -> CompileRW ExtComm
compileRule vs (RuleE ps) =
    let (pats,es) = unzip ps in
        compilePatterns vs pats >> completeExtComm vs es
compileRule vs (RuleC ps ec) = 
        compilePatterns vs ps >> gets vmap >>= \vm ->
        gets partIf <*> return (applySubstComm ec vm)

{- Agrega al estado las asignaciones de variables de los patrones y 
construye un comando If parcial, al que le falta el cuerpo -}
compilePatterns :: [Var] -> [Pattern] -> CompileRW ()
compilePatterns vs ps = void $ mapM (compilePattern . first V) (zip vs ps)

compilePattern :: (Expr,Pattern) -> CompileRW ()
compilePattern (e,p) =
    case p of
         PNil       -> modify (\s -> s { partIf = partIf s . IfElse e skip})
         PDot p1 p2 -> modify (\s -> s { partIf = partIf s . If e }) >>
                       compilePattern (Hd e,p1) >> compilePattern (Tl e,p2)
         PVar v     -> gets vmap >>= \vm ->
                       maybe (modify $ updvmap v) dupVarErr (M.lookup v vm)
    where
        dupVarErr = const $ lift $ Left "Error en pattern. Variable repetida"
        updvmap v s = s { vmap = M.insert v e (vmap s) }

{- Completa el comando if parcial obtenido con "compilePatterns", 
definiendo las asignaciones de variables con las expresiones del lado
derecho de la regla, a esas expresiones se les aplica la substitucion de
acuerdo a la asignacion de las variables de los patrones -}
completeExtComm :: [Var] -> [Expr] -> CompileRW ExtComm
completeExtComm vs es = foldr1 ESeq <$> mapM assignVar (zip vs es)
                                    <**> gets partIf

assignVar :: (Var,Expr) -> CompileRW ExtComm
assignVar (v,e) = gets vmap >>= \vm ->
                  return (EAssgn v (applySubstExpr e vm))

{- Substitución de variables en expresiones -}
applySubstExpr :: Expr -> M.Map Var Expr -> Expr
applySubstExpr var@(V v) vm   = fromMaybe var $ M.lookup v vm
applySubstExpr (Hd e) vm      = Hd $ applySubstExpr e vm
applySubstExpr (Tl e) vm      = Tl $ applySubstExpr e vm
applySubstExpr (Eq e e') vm   = Eq (applySubstExpr e vm)
                                   (applySubstExpr e' vm)
applySubstExpr (Cons e e') vm = Cons (applySubstExpr e vm)
                                     (applySubstExpr e' vm)
applySubstExpr (Univ e e') vm = Univ (applySubstExpr e vm)
                                     (applySubstExpr e' vm)
applySubstExpr e _ = e

{- Substitución de variables en comandos extendidos -}
applySubstComm :: ExtComm -> M.Map Var Expr -> ExtComm
applySubstComm (EAssgn v e) vm      = EAssgn v $ applySubstExpr e vm
applySubstComm (ESeq ec ec') vm     = ESeq (applySubstComm ec vm)
                                             (applySubstComm ec' vm)
applySubstComm (EWhile e ec) vm     = EWhile (applySubstExpr e vm)
                                               (applySubstComm ec vm)
applySubstComm (If e ec) vm         = If (applySubstExpr e vm)
                                           (applySubstComm ec vm)
applySubstComm (IfElse e ec ec') vm = IfElse (applySubstExpr e vm)
                                               (applySubstComm ec vm)
                                               (applySubstComm ec' vm)
applySubstComm (Rewrite vs rs) vm   = Rewrite vs $ applySubstRule rs vm
applySubstComm (Case v psec) vm     = Case v $ 
                                      map (second (`applySubstComm` vm)) psec
applySubstComm call@(Call {}) _     = call

applySubstRule :: [Rule] -> M.Map Var Expr -> [Rule]
applySubstRule rs vm = map applySubstRule' rs
    where
      applySubstRule' :: Rule -> Rule
      applySubstRule' (RuleE pses)  = RuleE $
                                      map (second (`applySubstExpr` vm)) pses
      applySubstRule' (RuleC ps ec) = RuleC ps $ applySubstComm ec vm
        
