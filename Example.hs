
module Example where

import Array


int0 = 0 :: Int
int1 = 1 :: Int

main0 xs = map head xs


main1 x = neq x
neq = not . eq
eq x = x == (0::Int)


main2 x y = neq2 (x::Int) y
neq2 x y = not (x == y)


main3 xs = (a . b . c) xs
a x = x+(1::Int)
b x = x*(4::Int)
c x = x-(3::Int)


main4 x = even (x :: Int)


main5 x = show (x :: Int)


main6 = show [()]


-- NOTE: Cannot be firstified
data Wrap a = Wrap (Wrap a) | Value a
f a = f (Wrap a)
main7 = f (Value id)


main8 = putChar 'x'


main9 = read "1" :: Int


main10 = app1 (gen1 ())
app1 (x,y) = x (y int0)
gen1 () = (id,id)


main11 xs = app (gen xs)
app [] = []
app (x:xs) = x (1::Int) : app xs
gen [] = []
gen (x:xs) = const x : gen xs


main12 = array (0,0) [(0::Int,0::Int)]


main13 = show (1 :: Double)
