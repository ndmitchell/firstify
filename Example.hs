
module Example where


{-
main xs = map head xs
-}

{-
main x = neq x
neq = not . eq
eq x = x == (0::Int)
-}

{-
main x y = neq (x::Int) y
neq x y = not (x == y)
-}

{-
main xs = (a . b . c) xs
a x = x+(1::Int)
b x = x*(4::Int)
c x = x-(3::Int)
-}

{-
main x = even (x :: Int)
-}

{-
main x = show (x :: Int)
-}

{-
main = show [()]
-}

{-
-- NOTE: Cannot be firstified
data Wrap a = Wrap (Wrap a) | Value a
f a = Wrap a
main = f (Value id)
-}

{-
main = putChar 'x'
-}

main = read "1" :: Int
