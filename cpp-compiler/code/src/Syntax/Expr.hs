{-# Language FlexibleInstances, UndecidableInstances #-}
module Syntax.Expr where

data Expr' a = Loc (Location' a)
             | MCall (MethodCall' a)
             | Lit a Literal
             | BOp a BinOp (Expr' a) (Expr' a)
             | UOp a UnOp (Expr' a)
    deriving (Eq,Ord)

data NoInfo = NI
    
type Expr = Expr' NoInfo

-- Variables
type Identifier = String

data Field' a = FId a Identifier
              -- Variables Array
              | FIdArray a Identifier (Expr' a)
    deriving (Eq,Ord)

type Field = Field' NoInfo

data Location' a = LBase (Field' a)
                 | LApp (Location' a) (Field' a)
    deriving (Eq,Ord)

type Location = Location' NoInfo
              
data MethodCall' a = MethodCall (Location' a) [Expr' a]
    deriving (Eq,Ord)

type MethodCall = MethodCall' NoInfo

data Literal = IntL Integer
             | FloatL Double
             | BoolL Bool 
             | StringL String
    deriving (Eq,Ord)
          
data BinOp = Arith ArithOp
           | Rel RelOp
           | Eq EqOp
           | Cond CondOp
    deriving (Eq,Ord)
           
data ArithOp = Plus | Min | Prod | Div | Mod
    deriving (Eq,Ord)

data RelOp = Lt | Gt | Leq | Geq
    deriving (Eq,Ord)

data EqOp = Equal | NEqual
    deriving (Eq,Ord)

data CondOp = And | Or
     deriving (Eq,Ord)

data UnOp = Neg | Not
    deriving (Eq,Ord)

idToLocation' :: a -> Identifier -> Location' a
idToLocation' a = LBase . FId a

idToLocation :: Identifier -> Location
idToLocation = LBase . FId NI
    
fieldName :: Field' a -> Identifier
fieldName (FId _ i) = i
fieldName (FIdArray _ i _) = i
    
locIdName :: Location -> Identifier
locIdName (LBase f) = fieldName f
locIdName (LApp _ f) = fieldName f
    
instance Show Field where
    show (FId _ i) = show i
    show (FIdArray _ i e) = show i ++ "[" ++ show e ++ "]"
    
instance Show Location where
    show (LBase f) = show f
    show (LApp l f) = show l ++ "." ++ show f

instance Show Literal where
    show (IntL i)    = show i
    show (FloatL d)  = show d
    show (BoolL b)   = show b
    show (StringL s) = show s
    
instance Show BinOp where
    show (Arith op) = show op
    show (Rel op)   = show op
    show (Eq op)    = show op
    show (Cond op)  = show op
          
instance Show ArithOp where
    show Plus = "+"
    show Min  = "-"
    show Prod = "*"
    show Div  = "/"
    show Mod  = "%"
           
instance Show RelOp where
    show Lt  = "<"
    show Gt  = ">"
    show Leq = "<="
    show Geq = ">="
           
instance Show EqOp where
    show Equal  = "=="
    show NEqual = "/="
           
instance Show CondOp where
    show And = "&&"
    show Or  = "||"
    
instance Show UnOp where
    show Neg = "-"
    show Not = "!"

instance Show MethodCall where
    show (MethodCall l es) = show l ++ parens (printEs es)
        where printEs :: [Expr] -> String
              printEs []        = ""
              printEs [e]       = show e
              printEs (e:_:es') = show e ++ "," ++ printEs es'

instance Show (Expr' NoInfo) where
    show (Loc l)    = show l
    show (MCall mc) = show mc
    show (Lit _ l)  = show l
    show (BOp _ bop e1 e2) = parens (show e1) ++ " " ++ show bop ++ " " ++ 
                             parens (show e2)
    show (UOp _ uop e)     = show uop ++ " " ++ parens (show e)


parens :: String -> String
parens s = "(" ++ s ++ ")"

instance Show NoInfo where
    show NI = ""
