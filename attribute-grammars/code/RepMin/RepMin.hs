module RepMin where

import Control.Arrow
import Data.Either

-- Binary Trees
data Tree =   Leaf Int
            | Bin (Tree,Tree)
            
-- Example
t :: Tree
t = Bin (Leaf 2,Bin (Bin (Bin (Bin (Leaf 5,Leaf 2),Leaf 3),Leaf 10),Leaf 4))

instance Show Tree where
    show (Leaf i)  = "Leaf " ++ show i
    show (Bin (l,r)) = "Bin " ++ "(" ++ show l ++ ") " ++ "(" ++ show r ++ ")"

-- Problem to solve: Replace value in leaves by least value
      
      
-- Functor FTree
type FTree a = Either Int (a,a)
      
type FTreeAlgebra a = FTree a -> a


-- Initial algebra, corresponding to syntax
init_algebra :: FTreeAlgebra Tree
init_algebra = either Leaf Bin

-- From another FTreeAlgebra, we obtain the unique morphism from
-- initial algebra.
cataTree :: FTreeAlgebra b -> Tree -> b
cataTree beta (Leaf i)    = beta (Left i)
cataTree beta (Bin (t1,t2)) = beta (Right (cataTree beta t1,cataTree beta t2))


-- First solution to RepMin problem
min_alg :: FTreeAlgebra Int
min_alg = either id (uncurry min)

rep_min_alg :: Int -> FTreeAlgebra Tree
rep_min_alg n = either (const $ Leaf n) Bin

replace_min :: Tree -> Tree
replace_min t = let n = cataTree min_alg t in
                    cataTree (rep_min_alg n) t
                    

-- Next step
rep_min_alg' :: FTreeAlgebra (Int -> Tree)
rep_min_alg' = either (const Leaf) 
                      (\(lfun,rfun) -> \m -> Bin (lfun m,rfun m))
                      
replace_min' :: Tree -> Tree
replace_min' t = (cataTree rep_min_alg' t) (cataTree min_alg t)


-- Tupled solution
infix 9 `x`


x :: FTreeAlgebra a -> FTreeAlgebra b -> FTreeAlgebra (a,b)
fa `x` fb = either (\i -> (fa $ Left i,fb $ Left i))
                   (\((a,b),(a',b')) ->
                      (fa $ Right (a,a'),fb $ Right (b,b')) )
                        

rep_min_alg'' :: FTreeAlgebra (Int,Int -> Tree)
rep_min_alg'' = min_alg `x` rep_min_alg'

replace_min'' :: Tree -> Tree
replace_min'' t = r m
    where (m, r) = cataTree rep_min_alg'' t

    
-- Next step

{- We want to transform (Int,Int -> Tree) into
   Int -> (Int,Tree).
-}

-- Get isomorphic algebra
getIsoAlg :: (a -> b) -> (b -> a) -> FTreeAlgebra a -> FTreeAlgebra b
getIsoAlg fab fba fa = either (fab . fa . Left)
                              (fab . fa . Right . (fba *** fba))

                              
-- The next functions aren't an isomorphism but
-- f2 . f1 = id
f1 :: (Int,Int -> Tree) -> (Int -> (Int,Tree))
f1 (i,f) = const i &&& f

f2 :: (Int -> (Int,Tree)) -> (Int,Int -> Tree)
f2 f = (fst (f 0),snd . f)

rep_min_alg''' :: FTreeAlgebra (Int -> (Int,Tree))
rep_min_alg''' = getIsoAlg f1 f2 rep_min_alg''


-- Final solution
replace_min''' :: Tree -> Tree
replace_min''' t = r
    where (m, r) = (cataTree rep_min_alg''' t) m
                 
