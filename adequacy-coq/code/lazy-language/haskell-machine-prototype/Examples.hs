module Examples where

import qualified Source  as T ( Term (Pair, Let, Fst, Snd) )
import qualified Machine as M ( Code (..), Val(..) )

import BinOps
import Source
import Machine
import Compiler

-- constante menos uno
cm10 :: Code
cm10 = V (C $ -1) 

c0 :: Code
c0 = V (C 0)

-- constante uno
c1 :: Code
c1 = V (C 1)

c3 :: Code
c3 = V (C 3)

-- sumar tres y tres
c6 :: Code
c6 = BOp Plus c3 c3

idGrab :: Code
idGrab = V $ Grab (A 0)

{- /////////////////////////////Example 1//////////////////////////////////

El ejemplo que se implementa a continuación es el siguiente:

      (Rec (\f -> \n -> if n == 0 then 0 else 2 + f (n-1))) 4

escrito en el lenguaje source sería

      Let ⌊4⌋ in
      Let λ (Ifz 0
                then ⌊0⌋
                else Let 1 + ⌊-1⌋
                     in (2 0) + ⌊2⌋
               ) in
      0 1

-}

-- Constante -1.
c_1 :: Code
c_1 = V (C $ -1)

c_2 :: Code
c_2 = V (C $ -2)

-- Constante 2.
c2 :: Code
c2 = V (C 2)

-- A 2 se corresponde con la llamada recursiva f, aplicada a n - 1.
appA2 :: Code
appA2 = Push 0 $ A 2

-- A 1 se corresponde con la variable n, le sumamos -1.
-- Notar que no es A 0, porque A 0 es la llamada recursiva de nuevo a
-- subs1ToA0.
subs1ToA0 :: Code
subs1ToA0 = BOp Plus (A 1) c_1

-- Pusheamos la resta n-1 para poder aplicarla en appA2.
letPush :: Code
letPush = M.Let (Rec subs1ToA0) (BOp Plus appA2 c2)

-- Acá es donde se ve que A 0, es n al contrario que en subs1ToA0 que es A 1.
ifZ :: Code
ifZ = IfZ (A 0) c0 letPush

funIfZ :: Code
funIfZ = V $ Grab ifZ

recFunIfZ :: Code
recFunIfZ = Rec funIfZ

-- Aplicamos recFunIfZ al valor 4.
appRecFunIfZ :: Code
appRecFunIfZ = M.Let (Rec $ V $ C 4) $
               M.Let recFunIfZ       $
               Push 1 $ A 0

-- Ejemplo completo.
computeAppRecFunIfZ :: IO ()
computeAppRecFunIfZ = compute defaultOpts $ initCfg appRecFunIfZ 

{- /////////////////////////////Example 2//////////////////////////////////

El ejemplo que se implementa a continuación es el siguiente (multiplicación):

      (Rec (\f -> \m -> \n -> if n == 0 then 0 else m + f m (n-1))) 2 4

escrito en el lenguaje source sería

      Let ⌊2⌋ in
      Let ⌊4⌋ in
      Let λ λ (Ifz 0
               then ⌊0⌋
               else Let 1 + ⌊-1⌋
                    in ((3 2) 0) + 2
              ) in
      (0 2) 1

-}

termMult :: Term
termMult = Lam $ Lam $
                  IfZero (Idx 0)
                         (Num 0)
                         (T.Let (BinOp Plus (Idx 1) (Num $ -1)) $
                                BinOp Plus (App (App (Idx 3) 2) 0) (Idx 2)
                         )

termAppMult :: Term
termAppMult = T.Let (Num 3)  $
              T.Let (Num 5)  $
              T.Let termMult $
              App (App (Idx 0) 2) 1

-- A 3 se corresponde con la llamada recursiva f, aplicada a m y n - 1.
appA3 :: Code
appA3 = Push 0 $ Push 2 $ A 3

-- Pusheamos la resta n-1 para poder aplicarla en appA3.
letPushMult :: Code
letPushMult = M.Let (Rec subs1ToA0) (BOp Plus appA3 (A 2))

-- Acá es donde se ve que A 0, es n al contrario que en subs1ToA0 que es A 1.
ifZMult :: Code
ifZMult = IfZ (A 0) c0 letPushMult

funIfZMult :: Code
funIfZMult = V $ Grab $ V $ Grab ifZMult

mult :: Code
mult = Rec funIfZMult

-- Aplicamos recFunIfZ' al valor 3 y 5, es decir 3*5.
appMult :: Code
appMult = M.Let (Rec $ V $ C 3) $
          M.Let (Rec $ V $ C 5) $
          M.Let mult            $
          Push 1 $ Push 2 $ A 0

appMult_lazy :: Code
appMult_lazy = M.Let (Rec c6)        $
               M.Let (Rec $ V $ C 2) $
               M.Let mult            $
               Push 1 $ Push 2 $ A 0


-- Ejemplo completo.
computeMult :: IO ()
computeMult = compute defaultOpts $ initCfg appMult

-- Ejemplo completo lazy.
computeMult_lazy :: IO ()
computeMult_lazy = compute defaultOpts $ initCfg appMult_lazy


{- /////////////////////////////Example 3//////////////////////////////////

El ejemplo que se implementa a continuación es el siguiente (exponenciación):

      (Rec (\f -> \m -> \n -> if n == 0 then 1 else m * f m (n-1))) 2 5

escrito en el lenguaje source sería (usando mult)

      Let ⌊2⌋ in
      Let ⌊4⌋ in
      Let mult in
      Let λ λ (Ifz 0
               then ⌊1⌋
               else Let 1 + ⌊-1⌋ in
                    Let (4 3) 1 in
                    (5 3) 0
              ) in
      (0 3) 2

-}

termExp :: Term
termExp = Lam $ Lam $
          IfZero (Idx 0)
                 (Num 1)
                 (T.Let (BinOp Plus (Idx 1) (Num $ -1)) $
                  T.Let (App (App (Idx 4) 3) 1)    $
                  App (App (Idx 5) 3) 0
                 )

termAppExp :: Term
termAppExp = T.Let (Num 2)  $
             T.Let (Num 5)  $
             T.Let termMult $
             T.Let termExp  $
             App (App (Idx 0) 3) 2

appA5 :: Code
appA5 = Push 0 $ Push 3 $ A 5

appA4 :: Code
appA4 = Push 1 $ Push 3 $ A 4

letPushExp :: Code
letPushExp = M.Let (Rec subs1ToA0) $
             M.Let (Rec appA4)     $
             appA5

ifZExp :: Code
ifZExp = IfZ (A 0) c1 letPushExp

funIfZExp :: Code
funIfZExp = V $ Grab $ V $ Grab ifZExp

expC :: Code
expC = Rec funIfZExp

appExp :: Code
appExp = M.Let (Rec $ V $ C 2) $
         M.Let (Rec $ V $ C 5) $
         M.Let mult            $
         M.Let expC            $
         Push 2 $ Push 3 $ A 0

-- Ejemplo completo.
computeExp :: IO ()
computeExp = compute defaultOpts $ initCfg appExp

{- /////////////////////////////Example 3//////////////////////////////////

El ejemplo que se implementa a continuación son las funciones
esPar y esImpar, escrito en el lenguaje source sería:

      Let λ Ifz 0
            then ⌊1⌋
            else IfZ 0 + ⌊-1⌋
                 then ⌊0⌋
                 else 0
      Let λ 0
      Let λ λ (Ifz (fst 1) 0
               then (⌊0⌋,⌊1⌋)
               else Ifz (snd 1) 0
                    then (⌊1⌋,⌊0⌋)
                    else
                    Let 1 + ⌊-1⌋ in
                    Let ((snd 3), (fst 3)) in
                    (4 0) 1
              ) in
      Let ⌊0⌋ in
      Let (3, 4) in
      (2 0) 1

-}

termOdd :: Term
termOdd = Lam $
          IfZero (Idx 0)
                 (Num 1)
                 (IfZero (BinOp Plus (Idx 0) (Num $ -1))
                         (Num 0)
                         (Idx 0)
                 )

termEven :: Term
termEven = Lam $ (Idx 0)

termRec :: Term
termRec = Lam $ Lam $
          IfZero (App (T.Fst 1) 0)
                 (T.Pair (Num 0) (Num 1))
                 (IfZero (App (T.Snd 1) 0)
                         (T.Pair (Num 1) (Num 0))
                         (T.Let (BinOp Plus (Idx 1) (Num $ -1))   $
                          T.Let (T.Pair (T.Snd 3) (T.Fst 3)) $
                          App (App (Idx 4) 0) 1
                         )
                 )

-- Esta termino retorna en la primera componente del par IsEven y en la
-- segunda IsOdd.
termAppPI :: Int -> Term
termAppPI n = T.Let termOdd  $                 -- 4
              T.Let termEven $                 -- 3
              T.Let termRec  $                 -- 2
              T.Let (Num n) $                 -- 1 | Argumento
              T.Let (T.Pair (Idx 3) (Idx 4)) $ -- 0
              App (App (Idx 2) 0) 1

termIsEven :: Term
termIsEven = T.Let termOdd  $
             T.Let termEven $
             T.Let termRec  $
             T.Let (Num 3)  $ -- Argumento
             T.Let (T.Pair (Idx 3) (Idx 4)) $
             T.Let (App (App (Idx 3) 1) 2)  $
             T.Fst 0

termIsOdd :: Term
termIsOdd = T.Let termOdd  $
            T.Let termEven $
            T.Let termRec  $
            T.Let (Num 8)  $ -- Argumento
            T.Let (T.Pair (Idx 3) (Idx 4)) $
            T.Let (App (App (Idx 3) 1) 2)  $
            T.Snd 0

computeAppPI :: Int -> IO ()
computeAppPI = compute defaultOpts . initCfg . compile . termAppPI

-- Implementación en Haskell
fix_poly :: ((Int -> Int, Int -> Int) -> Int -> (Int, Int))
         -> (Int -> Int, Int -> Int) -> Int -> (Int, Int)
fix_poly = \ f (p,i) n ->
             if p n == 0 then (0,1) else
             if i n == 0 then (1,0) else
             f (i, p) (n-1)

bpar :: Int -> Int
bpar 0 = 0
bpar 1 = 1
bpar n = n

bimpar :: Int -> Int
bimpar 0 = 1
bimpar 1 = 0
bimpar n = n

fix :: (a -> a) -> a
fix f = f (fix f)

parimpar :: Int -> (Int, Int)
parimpar = fix (fix_poly) (bpar,bimpar)

par :: Int -> Bool
par = (==0) . fst . parimpar

impar :: Int -> Bool
impar = (==0) . snd . parimpar

{- /////////////////////////////Example 4//////////////////////////////////

Segundo intento con una estrategia más general.

El ejemplo que se implementa a continuación son las funciones
esPar y esImpar, escrito en el lenguaje source sería:

      Let λ Ifz 0
            then ⌊1⌋
            else IfZ 0 + ⌊-1⌋
                 then ⌊0⌋
                 else 0
      Let λ 0
      Let λ λ (Ifz (fst 1) 0
               then (⌊0⌋,⌊1⌋)
               else Ifz (snd 1) 0
                    then (⌊1⌋,⌊0⌋)
                    else
                    Let 1 + ⌊-1⌋ in
                    Let ((snd 3), (fst 3)) in
                    (4 0) 1
              ) in
      Let ⌊0⌋ in
      Let (3, 4) in
      (2 0) 1

-}

-- Implementación en Haskell
-- For the case of mutually recursive clauses of the same type
fix_fst_arg :: (((a -> b) -> (a -> b) -> a -> b) ->
                ((a -> b) -> (a -> b) -> a -> b) ->
                a -> b) ->
               ((a -> b) -> (a -> b) -> a -> b) ->
               ((a -> b) -> (a -> b) -> a -> b) ->
               a -> b
fix_fst_arg f p i n = p (p (f p i) (f p i)) (i (f p i) (f p i)) n

fix_snd_arg :: (((a -> b) -> (a -> b) -> a -> b) ->
                ((a -> b) -> (a -> b) -> a -> b) ->
                a -> b) ->
               ((a -> b) -> (a -> b) -> a -> b) ->
               ((a -> b) -> (a -> b) -> a -> b) ->
               a -> b
fix_snd_arg f p i n = i (p (f p i) (f p i)) (i (f p i) (f p i)) n

espar :: Int -> Bool
espar = fix fix_fst_arg bpar2 bimpar2

esimpar :: Int -> Bool
esimpar = fix fix_snd_arg bpar2 bimpar2

bpar2 :: (Int -> Bool) -> (Int -> Bool) -> Int -> Bool
bpar2 p i n = if n == 0
              then True
              else i (n-1)

bimpar2 :: (Int -> Bool) -> (Int -> Bool) -> Int -> Bool
bimpar2 p i n = if n == 0
                then False
                else p (n-1)

{- /////////////////////////////Example 5//////////////////////////////////

Tercer intento con una estrategia con tuplas.

El ejemplo que se implementa a continuación son las funciones
esPar y esImpar, escrito en el lenguaje source sería:

      Let λ λ Ifz 0
              then ⌊0⌋
              else Let 1 + ⌊-1⌋ in
                   (snd 2) 0
      in Let λ λ Ifz 0
              then ⌊1⌋
              else Let 1 + ⌊-1⌋ in
                   (fst 2) 0
      in Let λ
             Let 2 0 in
             ((fst 1) 0 , (snd 1) 0)
      in Let ⌊8⌋                       -- Argumento
      in Let (4, 3)
      in 2 0

-}

termEvenProd :: Int -> Term
termEvenProd n = T.Let termProdEven             $
                 T.Let termProdOdd              $
                 T.Let termRecProd              $
                 T.Let (Num n)                  $ -- Argumento
                 T.Let (T.Pair (Idx 4) (Idx 3)) $
                 T.Let (App (Idx 3) 1)          $
                 App (T.Fst 0) 2

termOddProd :: Int -> Term
termOddProd n = T.Let termProdEven             $
                T.Let termProdOdd              $
                T.Let termRecProd              $
                T.Let (Num n)                  $ -- Argumento
                T.Let (T.Pair (Idx 4) (Idx 3)) $
                T.Let (App (Idx 3) 1)          $
                App (T.Snd 0) 2

termRecProd :: Term
termRecProd = Lam $
              (T.Let (App (Idx 2) 1) $
                T.Pair (App (T.Fst 1) 0) (App (T.Snd 1) 0)
              )

termProdEven :: Term
termProdEven = Lam $ Lam $
               IfZero (Idx 0)
                      (Num 0)
                      (T.Let (BinOp Plus (Idx 1) (Num $ -1)) $
                        App (T.Snd 2) 0
                      )

termProdOdd :: Term
termProdOdd = Lam $ Lam $
              IfZero (Idx 0)
                     (Num 1)
                     (T.Let (BinOp Plus (Idx 1) (Num $ -1)) $
                       App (T.Fst 2) 0
                     )             

computeAppEvenProd :: Int -> IO ()
computeAppEvenProd = compute defaultOpts . initCfg . compile . termEvenProd

computeAppOddProd :: Int -> IO ()
computeAppOddProd = compute defaultOpts . initCfg . compile . termOddProd


-- Implementación en Haskell
-- For the case of mutually recursive clauses of the same type
fix_prod :: (((a -> b,a -> b) -> a -> b
            ,(a -> b,a -> b) -> a -> b
            ) -> (a -> b, a -> b)) ->
            ((a -> b,a -> b) -> a -> b
            ,(a -> b,a -> b) -> a -> b
            ) -> (a -> b, a -> b)
fix_prod f (p, i) = (p (f (p, i)), i (f (p, i)))

parimpar_prod :: (Int -> Bool, Int -> Bool)
parimpar_prod = fix fix_prod (bpar3, bimpar3)

espar2 :: Int -> Bool
espar2 = fst parimpar_prod

esimpar2 :: Int -> Bool
esimpar2 = snd parimpar_prod

bpar3 :: (Int -> Bool,Int -> Bool) -> Int -> Bool
bpar3 (p, i) n = if n == 0
                 then True
                 else i (n-1)

bimpar3 :: (Int -> Bool,Int -> Bool) -> Int -> Bool
bimpar3 (p, i) n = if n == 0
                   then False
                   else p (n-1)


-- Generalización con listas
fix_polyl :: [[a]->a] -> [a]
fix_polyl fl = fix (\self -> map ($ self) fl)

-- /////////////////////////////Example 6//////////////////////////////////

termEx4 :: Term
termEx4 = T.Let (BinOp Plus (Num 1) (Num 2)) $
          T.Let (BinOp Plus (Num 1) (Num 2)) $
          (BinOp Plus (Idx 0) (Idx 0))

termEx4' :: Term
termEx4' = T.Let (BinOp Plus (Num 1) (Num 2)) $
           T.Let (App (Lam $ BinOp Plus (Idx 0) (Num 1)) 1) $
           (BinOp Plus (Idx 0) (Idx 1))

computeEx4 :: IO ()
computeEx4 = compute defaultOpts $ initCfg $ compile termEx4

computeEx4' :: IO ()
computeEx4' = compute defaultOpts $ initCfg $ compile termEx4'


-- /////////////////////////////Example 7//////////////////////////////////

-- let f = λn → if n=0 then 0 else n+f(n-1) in f 3
-- rec (λ ifz (A 0) (A 0) (BOp (A 0) (Let () (Push 0 (A 2)))
ifNZsum1 :: Code
ifNZsum1 = V (Grab (IfZ (A 0) (A 0)
                        (BOp Plus (A 0)
                         (M.Let (BOp Plus (A 1) c1) (Push 0 (A 2))))
                   )
             )

sumTill1 :: Code
sumTill1 = Rec ifNZsum1

-- ejemplo completo
example :: Code
example = M.Let (V (C 1)) (Push 0 sumTill1)

-- /////////////////////////////Example 8//////////////////////////////////

-- Fibonacci de n
-- Let ⌊n⌋ in
-- Let λ (Ifz 0
--            then ⌊0⌋
--       else Ifz 0 - ⌊1⌋
--            then ⌊1⌋
--            else Let 1 + ⌊-1⌋
--                 in Let 2 + ⌊-2⌋
--                    in (3 1) + (3 0)
--            ) in
-- 0 1

termFib :: Term
termFib = Lam $
          IfZero (Idx 0)
                 (Num 0)
          (IfZero (BinOp Plus (Idx 0) (Num $ -1))
                         (Num 1)
                         (T.Let (BinOp Plus (Idx 1) (Num $ -1)) $
                          T.Let (BinOp Plus (Idx 2) (Num $ -2)) $
                           BinOp Plus (App (Idx 3) 1) (App (Idx 3) 0)
                         )
                 )

termAppFib :: Int -> Term
termAppFib n = T.Let (Num n)  $
               T.Let termFib  $
               App (Idx 0) 1

-- Ejemplo completo.
computeAppFib :: Int -> IO ()
computeAppFib n = compute defaultOpts $ initCfg $ compile $ termAppFib n

-- /////////////////////////////Example 9//////////////////////////////////

-- Ejemplo de Sharing
-- Let ⌊3⌋ + ⌊4⌋ in
--   Let (A 1, A 1) in
--     Fst (A 0) + Snd (A 0)

termSharing :: Term
termSharing = T.Let (BinOp Plus (Num 3) (Num 4)) $
              T.Let (T.Pair (Idx 1) (Idx 1)) $
              BinOp Plus (T.Fst 0) (T.Fst 0)
              
-- Ejemplo completo.
follow :: [Pointer]
follow = [0..]

opts :: Options
opts = defaultOpts { withStep = False
                   , followedPointers = follow
                   }

computeSharing :: IO ()
computeSharing = compute opts $ initCfg $ compile $ termSharing


termTest :: Code
termTest = M.Let (M.Rec (V (M.Pair (M.A 0) (M.V (M.C 7))))) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Let (M.Fst 0) $
           M.Fst 0

computeTest :: IO ()
computeTest = compute opts $ initCfg $ termTest
