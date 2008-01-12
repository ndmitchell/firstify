
module Main(main) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import Control.Monad
import Yhc.Core
import Yhc.Core.Firstify
import System.FilePath
import System.Directory


data Actions = Reynolds | Mitchell | Stats | Help
             | Output String
             deriving (Show,Eq)


opts =
    [Option "r" ["reynolds"] (NoArg Reynolds) "Perform Reynolds defunctionalisation"
    ,Option "m" ["mitchell"] (NoArg Mitchell) "Perform Mitchell defunctionalisation"
    ,Option "s" ["stats"]    (NoArg Stats   ) "Show additional statistics"
    ,Option "o" []     (ReqArg Output "file") "Where to put the output file"
    ,Option "?" ["help"]     (NoArg Help    ) "Show help message"
    ]

pre = unlines 
    ["Firstify, (C) Neil Mitchell 2007-2008, University of York"
    ,""
    ,"    firstify file [flags]"
    ]
    

main = do
    args <- getArgs
    let (acts,files,errs) = getOpt Permute opts args

    when (Help `elem` acts) $ do
        putStr $ usageInfo pre opts
        exitWith ExitSuccess

    errs <- return $ ["No file specified" | null files] ++
                     ["Multiple files specified, only one is allowed" | length files > 1] ++
                     errs
    when (not $ null errs) $ do
        putStrLn "Errors occurred, try --help for further information"
        putStr $ unlines errs
        exitWith (ExitFailure 1)

    c <- loadCore $ head files
    
    when (Stats `elem` acts) $ showStats c

    c <- if Mitchell `notElem` acts then return c else do
        putStrLn "Performing Mitchell firstification"
        return $ firstify c

    when (Stats `elem` acts && Mitchell `elem` acts) $ showStats c

    c <- if Reynolds `notElem` acts then return c else do
        putStrLn "Performing Reynold's firstification"
        return $ reynolds c

    out <- case [o | Output o <- acts] of
               o:_ -> return o
               _ -> findOutput $ head files
    
    putStrLn "Writing result"
    saveCore out c


-- figure out where a file should go if we don't get an output location
findOutput s = return $ replaceBaseName s (takeBaseName s <.> "1st")


showStats :: Core -> IO ()
showStats c = putStrLn "Todo: Stats"
