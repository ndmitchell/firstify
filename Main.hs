
module Main(main) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import Control.Monad
import Yhc.Core
import Yhc.Core.Firstify


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
    putStrLn "Read file"
