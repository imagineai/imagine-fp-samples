{-# Language GADTs #-}
module Source where

import BinOps ( BinOperator )

type Index = Int

data Term where
  Unit   :: Term
  Idx    :: Index -> Term
  Num    :: Int   -> Term
  Lam    :: Term  -> Term
  App    :: Term  -> Index -> Term
  Let    :: Term  -> Term  -> Term
  Pair  :: Term  -> Term  -> Term
  Fst    :: Index -> Term
  Snd    :: Index -> Term
  BinOp  :: BinOperator -> Term  -> Term  -> Term
  IfZero :: Term  -> Term  -> Term -> Term
  deriving Show

data Type where
  TUnit :: Type
  TInt  :: Type
  TArr  :: Type -> Type -> Type
  TProd :: Type -> Type -> Type
