{- Módulo para definir la traducción de llamadas a macros a comandos
básicos, de acuerdo a la sección 2.1.7 -}
module ExtendedLanguage.Macro ( initStMacro
                              , replaceVars
                              , macroMaxvar) where

import Value ( Var )
import Expr ( Expr(..) )
import Prog

import qualified Data.Map as M
import Control.Applicative
import Control.Monad.State

data StateMacro = StateMacro { vmap   :: M.Map Var Var
                             {- Máxima variable para generar variables
                                frescas durante el proceso de reemplazo
                                de variables en una llamada a macro -}
                             , macroMaxvar :: Var
                             }

initStMacro :: (Var,Var) -> (Var,Var) -> Var -> StateMacro
initStMacro inpVars outVars mvar = 
    StateMacro { vmap        = M.fromList [inpVars,outVars]
               , macroMaxvar = mvar
               }
     
{- Mónada de estado -}
type CompileMacro a = State StateMacro a

updateSt :: Var -> Var -> CompileMacro ()
updateSt v w = gets vmap >>= \vm -> modify (upd vm)
    where
        upd :: M.Map Var Var -> StateMacro -> StateMacro
        upd vm st = st { vmap        = M.insert v w vm
                       , macroMaxvar = w
                       }

replaceVarsExpr :: Expr -> CompileMacro Expr
replaceVarsExpr (V v) = gets vmap >>= \vm ->
                        case M.lookup v vm of
                            Just w  -> return $ V w
                            Nothing -> gets macroMaxvar >>= \maxVar ->
                                       updateSt v (maxVar+1) >>
                                       return (V $ maxVar+1)
replaceVarsExpr (Cons e e') = Cons <$> replaceVarsExpr e <*> replaceVarsExpr e'
replaceVarsExpr (Hd e)      = Hd   <$> replaceVarsExpr e
replaceVarsExpr (Tl e)      = Tl   <$> replaceVarsExpr e
replaceVarsExpr (Eq e e')   = Eq   <$> replaceVarsExpr e <*> replaceVarsExpr e'
replaceVarsExpr (Univ e e') = Univ <$> replaceVarsExpr e <*> replaceVarsExpr e'
replaceVarsExpr e           = return e

replaceVars :: Comm -> CompileMacro Comm
replaceVars (Assgn v e) =
                gets vmap >>= \vm ->
                case M.lookup v vm of
                    Just w  -> Assgn w <$> replaceVarsExpr e
                    Nothing -> gets macroMaxvar >>= \maxVar ->
                               updateSt v (maxVar+1) >>
                               Assgn (maxVar+1) <$> replaceVarsExpr e
replaceVars (Seq c c')  = Seq    <$> replaceVars c     <*> replaceVars c'
replaceVars (While e c) = While  <$> replaceVarsExpr e <*> replaceVars c
