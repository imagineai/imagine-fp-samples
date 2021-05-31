module Examples where

import Lambda
import Parser

examples :: [Term]
examples = [ identity
           , first, second
           , application
           , twice, thrice
           , comp
           --, delta
           --, ycomb
           , t1, t2, t2', t3
           ]

-- Examples

-- \x -> x
identity = Abs "x" (Id "x")

-- \x y -> x
first = Abs "x" (Abs "y" (Id "x"))

-- \x y -> y
second = Abs "x" (Abs "y" (Id "x"))

-- \f x -> f x
application = Abs "f" (Abs "x" (App (Id "f") (Id "x")))

-- \f x -> f (f x)
twice = Abs "f" (Abs "x" (App (Id "f") (App (Id "f") (Id "x"))))

-- \f x -> f (f (f x))
thrice = Abs "f" (Abs "x" (App (Id "f") (App (Id "f") (App (Id "f") (Id "x")))))

-- \g f x -> g (f x)
comp = Abs "g" (Abs "f" (Abs "x" (App (Id "g") (App (Id "f") (Id "x")))))

-- \x -> x x
delta = Abs "x" (App (Id "x") (Id "x"))

-- \f -> (\x-> f (x x)) (\x-> f (x x))
ycomb = Abs "f" (App st st)
    where st = Abs "x" (App (Id "f") (App (Id "x") (Id "x")))

-- \x f g -> f g (x g) 
t1 = Abs "x" (Abs "f" (Abs "g" (App (App (Id "f") (Id "g")) (App (Id "x") (Id "g")))))

-- \x y f -> f (x (\w -> f w)) (y f x)
t2 = Abs "x" (Abs "y" (Abs "f" (App st1 st2)))
    where
        st1 = App (Id "f") (App (Id "x") stw)
        stw = Abs "w" (App (Id "f") (Id "w"))
        st2 = App (App (Id "y") (Id "f")) (Id "x")

t2' = Abs "x" (Abs "y" (Abs "f" (App st1 st2)))
    where
        st1 = App (Id "f") (App (Id "x") stw)
        stw = Abs "w" (App (Id "f") (Id "w"))
        st2 = App (App (App (Id "y") (Id "f")) (Id "x")) (Id "x")
    
-- \x y f g h -> (h (f x)) (g y)
t3 = Abs "x" (Abs "y" (Abs "f" (Abs "g" (Abs "h" (App st1 st2)))))
    where
        st1 = App (Id "h") (App (Id "f") (Id "x"))
        st2 = App (Id "g") (Id "y")
        
        
        