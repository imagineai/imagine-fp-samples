{-# Language RankNTypes #-}
{- Data values del lenguaje While de acuerdo al libro 
   "Computability and Complexity" de Neil Jones.
   Los valores del lenguaje son árboles construidos a partir
   de un conjunto finito -}

module Value ( Atom (..) 
             , Value (..)
             , nil, dtrue, dfalse
             , (·)
             , iToV
             , vToNat
             , printAsLList
             , Var
             , valueToTree
             , oneVar
             ) where

import Data.Tree ( Tree(..) )
                 
-- Las variables seran numeros naturales
type Var = Int

data Atom =  Nil
    deriving Eq
    
instance Show Atom where
    show Nil = "nil"

data Value = VAtom Atom | Dot Value Value
    deriving Eq
    
instance Show Value where
    show (VAtom a) = show a
    show (Dot v1 v2) = "(" ++ show v1 ++ 
                       " . " ++ show v2 ++
                       ")" 
    
-- una variable cualquiera
oneVar :: Var
oneVar = 1

valueToTree :: Value -> Tree String
valueToTree (VAtom a)  = Node (show a) []
valueToTree (Dot v v') = Node "|" [ valueToTree v
                                  , valueToTree v'
                                  ]

nil :: Value
nil = VAtom Nil

infixl 7 ·
(·) :: Value -> Value -> Value
a · b = Dot a b

{- Definición de true y false -}
dtrue :: Value
dtrue = nil · nil

dfalse :: Value
dfalse = nil

{- Conversión entre enteros y Value -}
iToV :: Int -> Value
iToV n | n < 0     = iToVneg (-1 * n)
       | otherwise = iToVpos n
    
iToVpos :: Int -> Value
iToVpos 0     = nil
iToVpos n = nil · iToVpos (n-1)

iToVneg :: Int -> Value
iToVneg 0 = nil · nil
iToVneg n = iToVneg (n-1) · nil

vToNat :: Value -> Maybe Int
vToNat (VAtom Nil) = Just 0
vToNat (Dot (VAtom Nil) v) = vToNat v >>= Just . (+1)
vToNat (Dot _ _)   = Nothing

printAsRList :: Value -> String
printAsRList (VAtom Nil) = error "Imposible: printAsRList"
printAsRList (Dot v (VAtom _)) = printAsLList v
printAsRList (Dot v v') = printAsLList v ++ " " ++ printAsRList v'

printAsLList :: Value -> String
printAsLList (VAtom a) = show a
printAsLList (Dot v (VAtom _)) = "(" ++ printAsLList v ++ ")"
printAsLList (Dot v v') = "(" ++ printAsLList v ++ " " ++ printAsRList v' ++ ")"
