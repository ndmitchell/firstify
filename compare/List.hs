
module Main where

import System

main = do
    [sn] <- getArgs
    let n = read sn
        res = if n > 0
              then list    $ build (abs n) snoc nil
              else reverse $ build (abs n) (:)  []
    print $ length res    


build :: Int -> (Char -> b -> b) -> b -> b
build 0 f x = x
build n f x = build (n-1) f $! f 'a' x



nil = id
snoc x xs = \ys -> xs (x:ys)
list xs = xs []
