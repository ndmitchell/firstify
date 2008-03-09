
module Main where

import System
import Monad


main = do
    [n,s] <- getArgs
    src <- liftM (concat . replicate (read n)) $ readFile "Sort.hs"
    let t = test ((if s == "yhc" then sortByYhc else if s == "ghc" then sortByYhc2 else undefined) compare)
    t src
    t src
    t src

test sort = print . ordered . sort . sort . reverse . sort


ordered (x:y:xs) = x <= y && ordered (y:xs)
ordered _ = True


sortByYhc :: (a -> a -> Ordering) -> [a] -> [a]
sortByYhc cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as
  
sortByYhc2 :: (a -> a -> Ordering) -> [a] -> [a]
sortByYhc2 cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b [a] xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (a:as) bs
    ascending a as bs   = rev2 as [a] : sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as

rev x = rev2 x []
rev2 (x:xs) y = rev2 xs (x:y)
rev2 [] y = y
  

sortByGHC :: (a -> a -> Ordering) -> [a] -> [a]
sortByGHC cmp = mergesort' cmp . map wrap
    where
        mergesort' :: (a -> a -> Ordering) -> [[a]] -> [a]
        mergesort' cmp [] = []
        mergesort' cmp [xs] = xs
        mergesort' cmp xss = mergesort' cmp (merge_pairs cmp xss)

        merge_pairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
        merge_pairs cmp [] = []
        merge_pairs cmp [xs] = [xs]
        merge_pairs cmp (xs:ys:xss) = merge cmp xs ys : merge_pairs cmp xss

        merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
        merge cmp [] ys = ys
        merge cmp xs [] = xs
        merge cmp (x:xs) (y:ys)
         = case x `cmp` y of
                GT -> y : merge cmp (x:xs)   ys
                _  -> x : merge cmp    xs (y:ys)

        wrap :: a -> [a]
        wrap x = [x]
