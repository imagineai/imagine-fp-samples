{-# Language GADTs #-}
module BinOps where

data BinOperator where
  Plus  :: BinOperator
  Minus :: BinOperator
  deriving Eq

semBOp :: BinOperator -> (Int -> Int -> Int)
semBOp Plus = (+)
semBOp Minus = (-)

instance Show BinOperator where
  show Plus = "+"
  show Minus = "-"
