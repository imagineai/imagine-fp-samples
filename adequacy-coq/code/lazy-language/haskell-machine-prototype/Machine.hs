{-# Language GADTs, TypeSynonymInstances, FlexibleInstances #-}
module Machine where

import BinOps ( BinOperator (..), semBOp )
import Prelude hiding ( log , filter )
import Control.Monad.IO.Class ( liftIO )
import Data.Map ( Map, insert, (!?), fromList, empty, filter
                , foldrWithKey, filterWithKey
                )
import Control.Monad.Trans.RWS.Lazy ( RWST, runRWST, get, put, ask )

import System.IO

data Val where
  U    :: Val                 -- ^ unit
  C    :: Int -> Val          -- ^ constant
  Grab :: Code -> Val         -- ^ abstraction
  Pair :: Code -> Code -> Val -- ^ pairs
  deriving (Show, Eq)

data Code where
  V    :: Val  -> Code         -- ^ values
  A    :: Int  -> Code         -- ^ access (variables)
  BOp  :: BinOperator -> Code -> Code -> Code -- ^ binary operator
  Push :: Int  -> Code -> Code 
  Let  :: Code -> Code -> Code
  Fst  :: Int  -> Code
  Snd  :: Int  -> Code
  IfZ  :: Code -> Code -> Code -> Code
  Rec  :: Code -> Code
  deriving (Show, Eq)

type Pointer = Int

data Marker where
  Up  :: Pointer -> Marker
  UpL :: Pointer -> Marker
  UpR :: Pointer -> Marker
  If  :: Pointer -> Marker
  Op  :: BinOperator -> Pointer -> Marker

instance Show Marker where
  show (Up p)  = "#" ++ show p
  show (UpL p) = "#₁" ++ show p
  show (UpR p) = "#₂" ++ show p
  show (If p)  = "?" ++ show p
  show (Op bop p)  = show bop ++ show p

data Cont where
  IfC  :: Code -> Code -> Cont
  BOpL :: BinOperator -> Code -> Cont
  BOpR :: BinOperator -> Val  -> Cont
  deriving Show

type MEnv = [Pointer]

data Projection = L | R

instance Show Projection where
  show L = "1"
  show R = "2"

data StackE where
  P  :: Pointer    -> StackE
  M  :: Marker     -> StackE
  Pj :: Projection -> StackE

instance Show StackE where
  show (P p)  = "p" ++ show p
  show (M p)  = show p
  show (Pj p) = "π" ++ show p

type Stack = [StackE]

data MClos where
  IClos :: Code -> MEnv -> MClos
  CClos :: Cont -> MEnv -> MClos
  deriving Show

type Heap = Map Pointer MClos

instance {-# OVERLAPPING #-} Show Heap where
  show m = "{" ++ foldrWithKey showPointerMClos "" m ++ "}"
    where showPointerMClos :: Pointer -> MClos -> String -> String
          showPointerMClos p (IClos i env) str =
            ("\x1b[32;107m" ++ show p ++ "\x1b[0m\x1b[32m") ++
            " ↣ " ++ show (i,env) ++ ", " ++ str
          showPointerMClos p (CClos i env) str =
            show p ++ " ↣ " ++ show (i,env) ++ ", " ++ str

type Conf = (Heap,Code,MEnv,Stack)

instance {-# OVERLAPPING #-} Show Conf where
  show (h,c,env,s) =
    "(" ++ "\x1b[32m" ++ show h   ++ "\x1b[0m" ++
    "," ++ "\x1b[36m" ++ show c   ++ "\x1b[0m" ++
    "," ++ "\x1b[91m" ++ show env ++ "\x1b[0m" ++
    "," ++ "\x1b[35m" ++ show s   ++ "\x1b[0m" ++
    ")"

type NextFreePointer = Pointer

isIClos :: MClos -> Bool
isIClos (IClos _ _) = True
isIClos (CClos _ _) = False

uHeap :: Heap -> Pointer -> MClos -> Heap
uHeap h p c = insert p c h

data Options = Options
               { withStep         :: Bool
               , followedPointers :: [Pointer]
               , logFun           :: [Pointer] -> Conf -> RuleName -> IO ()
               }

type Compute a = RWST Options () NextFreePointer IO a

getFreshPointer :: Compute Pointer
getFreshPointer = get >>= \fp -> put (fp+1) >> return fp

type RuleName = String

fullLog :: Conf -> RuleName -> IO ()
fullLog w rule = putStrLn  ("—{" ++ rule ++ "}→") >> putStrLn (show w)

codeStackLog :: [Pointer] -> Conf -> RuleName -> IO ()
codeStackLog _ (_,c,_,s) rule = liftIO (putStrLn  ("—{" ++ rule ++ "}→") >>
                                      putStrLn (show (c,s)))

fullLogWithPartialHeap :: [Pointer] -> Conf -> RuleName -> IO ()
fullLogWithPartialHeap _ (h,c,env,s) = fullLog (h',c,env,s)
  where h' :: Heap
        h' = filter isIClos h

fullLogWithVarFollowHeap :: [Pointer] -> Conf -> RuleName -> IO ()
fullLogWithVarFollowHeap follows (h,c,env,s) = fullLog (h',c,env,s)
  where h' :: Heap
        h' = filterWithKey isInFollows h
        isInFollows :: Pointer -> MClos -> Bool
        isInFollows p (IClos _ _) = elem p follows
        isInFollows _ (CClos _ _) = False


logIO :: Conf -> RuleName -> Compute ()
logIO w r = ask >>= \opts -> step >>
                            (liftIO (logFun opts (followedPointers opts) w r))
  where step :: Compute ()
        step = ask >>= \opts -> if withStep opts
                                then stopExec
                                else return ()

trans :: Conf -> Compute Conf
-- After reaching a value, we update the heap.
trans (h, (V iv), env, M (Up p) : s) =
  let w = (uHeap h p (IClos (V iv) env), (V iv), env, s)
  in logIO w "Upd" >> trans w
-- Updating the first component of a pair.
trans (h, (V iv), env, M (UpL p) : s) =
  case h !? p of
    Just (IClos (V (Pair _ i')) env') ->
      let w = (uHeap h p (IClos (V (Pair (V iv) i')) env'), (V iv), env, s)
      in logIO w "Upd1" >> trans w
    _ -> error "Impossible"
-- Updating the second component of a pair.    
trans (h, (V iv), env, M (UpR p) : s) =
  case h !? p of
    Just (IClos (V (Pair i _)) env') ->
      let w = (uHeap h p (IClos (V (Pair i (V iv))) env'), (V iv), env, s)
      in logIO w "Upd2" >> trans w
    _ -> error "Impossible"
-- We have an integer value and we are computing an operation.    
trans (h, (V (C n)), env', M (Op _ p) : s) =
  -- El puntero al operador que tenemos en el tope del stack
  -- podría llegar a ser distinto del que encontramos al desreferenciar
  -- p; esto no ocurre cuando el código es resultado de compilar
  -- un termino bien tipado.
  case h !? p of
    Just (CClos (BOpL bop i) env) ->
      let w = (uHeap h p (CClos (BOpR bop (C n)) env'), i, env
              , M (Op bop p) : s)
      in logIO w "FOp" >> trans w
    Just (CClos (BOpR bop (C m)) env) ->
      let w = (uHeap h p (IClos (V (C $ (semBOp bop) n m)) env')
              , (V (C $ (semBOp bop) n m)), env, s)
      in logIO w "SOp" >> trans w
    _ -> error "Impossible"
-- We have an integer value to choose the branch of a conditional
trans (h, (V (C n)), _, M (If p) : s) =
  case (n, h !? p) of
    (0, Just (CClos (IfC i _) env')) ->  let w = (h, i, env', s)
                                         in logIO w "isZ" >> trans w
    (_, Just (CClos (IfC _ i') env')) -> let w = (h, i', env', s)
                                         in logIO w "isS" >> trans w
    _ -> error "Impossible"
trans (h, (V (Grab i)), env, (P p) : s) =
  let w = (h, i, p : env, s)
  in logIO w "Grab" >> trans w
trans (h, (A n), env, s) =
  let p = (env !! n) in
  case h !? p of
    Just (IClos i env') ->
      let w = (h, i, env', M (Up p) : s)
      in logIO w "Acc" >> trans w
    _ -> error "Impossible"
trans (h, (Push n i), env, s) =
  let p = (env !! n)
      w = (h, i, env, P p : s)
  in logIO w "Push" >> trans w
trans (h, (Let i i'), env, s) =
  getFreshPointer >>= \ fp ->
  let w = (uHeap h fp (IClos i env), i', fp : env, s)
  in logIO w "Let" >> trans w
trans (h, (BOp bop i i'), env, s) =
  getFreshPointer >>= \ fp ->
  let w = (uHeap h fp (CClos (BOpL bop i') env), i, env, M (Op bop fp) : s)
  in logIO w "BOp" >> trans w
trans (h, (IfZ i i' i''), env, s) =
  getFreshPointer >>= \ fp ->
  let w = (uHeap h fp (CClos (IfC i' i'') env), i, env, M (If fp) : s)
  in logIO w "Ifz" >> trans w
trans (h, (Fst n), env, s) =
  let p = (env !! n) in
  case h !? p of
    Just (IClos i env') ->
      let w  = (h, i, env', M (Up p) : Pj L : M (UpL p) : s)
      in logIO w "Fst" >> trans w
    _ -> error "Impossible"
trans (h, (Snd n), env, s) =
  let p = (env !! n) in
  case h !? p of
    Just (IClos i env') ->
      let w = (h, i, env', M (Up p) : Pj R : M (UpR p) : s)
      in logIO w "Snd" >> trans w
    _ -> error "Impossible"
trans (h, V (Pair i _), env, Pj L : s) =
  let w = (h, i, env, s)
  in logIO w "Pi1" >> trans w
trans (h, V (Pair _ i'), env, Pj R : s) =
  let w = (h, i', env, s)
  in logIO w "Pi2" >> trans w
trans (h, Rec i, env, s) =
  getFreshPointer >>= \ fp ->
  let w = (uHeap h fp (IClos (Rec i) env), i, fp : env, s)
  in logIO w "Rec" >> trans w
trans w = liftIO (putStrLn "\nFinal conf:") >> return w

eHeap :: Heap
eHeap = empty

initCfg :: Code -> Conf
initCfg c = (eHeap, c, [], [])

takeCodefromConf :: Conf -> Code
takeCodefromConf (_,i,_,_) = i

log :: [Pointer] -> Conf -> RuleName -> IO ()
log fp = fullLogWithVarFollowHeap fp

defaultOpts :: Options
defaultOpts = Options { withStep         = False
                      , followedPointers = [0..]
                      , logFun           = log 
                      }

compute :: Options -> Conf -> IO ()
compute ops w = putStrLn (unlines
              [ ""
              , "Initial conf:"
              , show w
              ]) >>
                runRWST (trans w) ops 0 >>=
                \(w',_,_) ->
                  putStrLn (unlines
              [ show w'
              , ""
              , show . takeCodefromConf $ w
              , "⟼  *"
              , show . takeCodefromConf $ w'
              ])

stopExec :: Compute ()
stopExec = liftIO (hGetChar stdin) >> return ()
