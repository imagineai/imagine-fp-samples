{- Módulo que define la traducción del lenguaje extendido
   al lenguaje base WHILE -}
module ExtendedLanguage.Compiler ( compileEProg
                                 , CompError) where

import Expr (Expr (V))
import Prog
import Value (Var)
import ExtendedLanguage.ExtLanguage
import ExtendedLanguage.Rewrite
import ExtendedLanguage.Macro

import Prelude hiding (read)
import qualified Data.Map as M
import Control.Monad.State
import Control.Arrow
import Control.Applicative ( (<$>), (<*>) )

{- Traduce del lenguaje extendido al base.
   Se requiere la máxima variable usada para poder crear
   variables frescas durante la traducción. -}
   
compileEProg :: ExtProg -> ProgNames -> Either CompError Prog
compileEProg (ExtProg v ec w mvar) eps = 
    either Left mkprog (evalStateT (compileEComm ec) initStateCompile)
    where mkprog c = return Prog { read  = v
                                 , prg   = c
                                 , write = w
                                 }
          initStateCompile = StateCompile { cmaxvar = mvar
                                          , xprogs  = eps
                                          }

data StateCompile = StateCompile { {- Máxima variable actualizada durante la 
                                      transformación de un comando (por ejemplo,
                                      el comando if genera nuevas
                                      variables )
                                   -}
                                   cmaxvar :: Var
                                 , xprogs  :: M.Map Name ExtProg
                                 }

type Compile a = StateT StateCompile (Either CompError) a
   
compileEComm :: ExtComm -> Compile Comm
compileEComm (EAssgn v e)     = return (Assgn v e)
compileEComm (ESeq ec1 ec2)   = Seq <$> compileEComm ec1 <*> compileEComm ec2
compileEComm (EWhile e c)     = While e <$> compileEComm c
compileEComm (If e c)         = compileIf e c 
compileEComm (IfElse e c1 c2) = compileIfElse e c1 c2
compileEComm (Rewrite vs rs)  = either (lift . Left) compileEComm
                                (evalStateT (compileRewrite vs rs) initStateRW)
compileEComm (Case w ps)      = either (lift . Left) compileEComm
                                (evalStateT (compileCase w ps) initStateRW)
    where compileCase w' ps' = compileRewrite [w'] 
                               (map (\(p,ec) -> RuleC [p] ec) ps')
compileEComm (Call b name a)  = compileMacro b name a

{- Condicional -}
compileIf :: Expr -> ExtComm -> Compile Comm
compileIf e ec =
        (+1) <$> gets cmaxvar >>= \z ->
        modify (updateCMaxVar z) >> compileEComm ec >>= \c ->
                 return $ Assgn z e <.> While (V z) (Assgn z efalse <.> c)

compileIfElse :: Expr -> ExtComm -> ExtComm -> Compile Comm
compileIfElse e ec1 ec2 = 
        ((+1) &&& (+2)) <$> gets cmaxvar >>= \(z,w) ->
        modify (updateCMaxVar w) >> compileEComm ec1 >>= \c1 -> 
        compileEComm ec2 >>= \c2 -> 
        return $ 
             Assgn z e <.> 
             Assgn w etrue <.> 
             While (V z) (Assgn z efalse <.> Assgn w efalse <.> c1) <.>
             While (V w) (Assgn w efalse <.> c2)
     
compileMacro :: Var -> Name -> Var -> Compile Comm
compileMacro b name a = 
        getProg name >>= \xp ->
        localState (compileEComm $ xcomm xp) 
                   (replaceMaxVar $ maxvar xp)
        >>= \comm -> gets cmaxvar >>= \mvar ->
        let (c,updmvar) = runReplaceVars xp comm mvar in
            modify (updateCMaxVar (updmvar+1)) >> return c
    where runReplaceVars :: ExtProg -> Comm -> Var -> (Comm,Var)
          runReplaceVars xp comm mvar = 
                second macroMaxvar $ 
                runState (replaceVars comm) 
                         (initStMacro (xread xp,a) (xwrite xp,b) mvar)
          replaceMaxVar :: Var -> StateCompile -> StateCompile
          replaceMaxVar v st = st { cmaxvar = v }

     
-- funciones auxiliares
updateCMaxVar :: Var -> StateCompile -> StateCompile
updateCMaxVar v st = st { cmaxvar = v }

getProg :: Name -> Compile ExtProg
getProg name = gets xprogs >>= 
               maybe (lift $ Left (name ++ " no refiere a un programa."))
                     return . M.lookup name
                   
{- Computa una mónada ca en el estado st, devuelve el valor
y restablece el estado anterior a la computación. -}
localState :: Compile a -> (StateCompile -> StateCompile) -> Compile a
localState ca f = 
    get >>= \storig -> modify f >> ca >>= \a ->
    put storig >> return a
