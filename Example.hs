
module Example where


{-
main xs = map head xs
-}

{-
main x = neq x
neq = not . eq
eq x = x == (0::Int)
-}

main x y = neq (x::Int) y
neq x y = not (x == y)
