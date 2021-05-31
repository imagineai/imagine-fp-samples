module Eval ( evalProg, EvalError ) where

import Expr  ( Expr(..) )
import Prog  ( Prog(..)
             , Comm(..)
             )
import ProgAsValue ( progToValue, valueToProg )
import Value ( Var, Value(..), (·)
             , dtrue, dfalse, nil
             )

import qualified Data.Map as M ( Map
                               , lookup, insert
                               , fromList
                               )

import Control.Arrow ( first )
import Control.Applicative ( (<$>), (<*>) )
import Control.Monad.Trans ( lift )
import Control.Monad.Fix ( fix )
import Control.Monad.RWS ( RWST
                         , get, ask, put
                         , runRWST
                         , unless
                         )

type State     = M.Map Var Value
type EvalError = String

-- R: Prog.
-- W: Se podría agregar la traza de evaluación.
-- S: Var |-> Value.
-- m: Maybe, se puede llegar a cambiar por una mónada.
--    que reporte mejores errores.
type EvalState a = RWST Value () State (Either EvalError) a

varDoesntExist :: Int -> Either String a
varDoesntExist v = Left $ "La variable " ++ show v ++ " no esta declarada."

varExistsAndIsNil :: Int -> Either EvalError Value
varExistsAndIsNil = Right . const nil

invalidDataAsProg :: Either String a
invalidDataAsProg = Left $ unwords [ "El primer argumento del Univ"
                                   , "no se corresponde con un programa valido."
                                   ]

evalExpr :: Expr -> EvalState Value
evalExpr (V v)       = get >>= 
                       maybe (lift $ varExistsAndIsNil v) return . M.lookup v
evalExpr (A a)       = return $ VAtom a
evalExpr (Cons e e') = (·) <$> evalExpr e <*> evalExpr e'
evalExpr (Hd e)      = evalExpr e >>= takeHd
evalExpr (Tl e)      = evalExpr e >>= takeTl
evalExpr (Eq e e')   = checkEq <$> evalExpr e <*> evalExpr e'
evalExpr Star        = ask
evalExpr (Univ e e') = curry (first valueToProg) <$> evalExpr e <*> evalExpr e'
                       >>= checkProg >>= lift . uncurry evalProg

evalComm :: Comm -> EvalState ()
evalComm (Assgn v e) = get >>= \st ->
                       evalExpr e >>= put . flip (M.insert v) st
evalComm (Seq c c')  = evalComm c >> evalComm c'
evalComm (While e c) = fix while
    where
        while :: EvalState () -> EvalState ()
        while es = evalExpr e >>= \d -> unless (d == nil) $ evalComm c >> es

evalProg :: Prog -> Value -> Either EvalError Value
evalProg p@(Prog x c y) d = 
         case runRWST (evalComm c) (progToValue p) st of
             Right (_,st',_) -> maybe (varDoesntExist y) return $ M.lookup y st'
             Left err        -> Left err
    where
        st :: State
        st = M.fromList [(x,d)]

-- Funciones auxiliares.

checkEq :: Value -> Value -> Value
checkEq d d' | d == d'   = dtrue
             | otherwise = dfalse

checkProg :: (Maybe Prog, Value) -> EvalState (Prog, Value)
checkProg (Just p, d)  = return (p, d)
checkProg (Nothing, _) = lift invalidDataAsProg

takeHd :: Value -> EvalState Value
takeHd (Dot h _) = return h
takeHd _         = return nil

takeTl :: Value -> EvalState Value
takeTl (Dot _ t) = return t
takeTl _         = return nil
