
module Main(main) where

import Control.Monad
import Data.List
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import Yhc.Core
import Yhc.Core.Firstify
import qualified Data.Map as Map
import qualified Data.Set as Set


data Actions = Reynolds | Mitchell | Stats | Help
             | Output String | Text | Html
             deriving (Show,Eq)


opts =
    [Option "r" ["reynolds"] (NoArg Reynolds) "Perform Reynolds defunctionalisation"
    ,Option "m" ["mitchell"] (NoArg Mitchell) "Perform Mitchell defunctionalisation"
    ,Option "s" ["stats"]    (NoArg Stats   ) "Show additional statistics"
    ,Option "o" []     (ReqArg Output "file") "Where to put the output file"
    ,Option "t" ["text"]     (NoArg Text    ) "Output a text file of the Core"
    ,Option "h" ["html"]     (NoArg Html    ) "Output an HTML file of the Core"
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
    when (Text `elem` acts) $ writeFile (out <.> "txt") (show c)
    when (Html `elem` acts) $ writeFile (out <.> "htm") (coreHtml c)


-- figure out where a file should go if we don't get an output location
findOutput s = return $ replaceBaseName s (takeBaseName s <.> "1st")


-- statistics:
--    how many functions are under/over-staturated when applied
--        both instances, and how many functions
--    how many higher-order applications are there
showStats :: Core -> IO ()
showStats c = putStr $ unlines
        ["Higher-Order Statistics"
        ,"HO Applications: " ++ pad hoApp
        ,"Under-Sat calls: " ++ pad (length under)
        ,"Under-Sat funs : " ++ pad (g under)
        ,"Over -Sat calls: " ++ pad (length over)
        ,"Over -Sat funs : " ++ pad (g over)
        ]
    where
        arity = Map.fromList [(coreFuncName x, coreFuncArity x) | x <- coreFuncs c]

        c2 = transformExpr appRules c

        -- use all the CoreApp properties
        -- plus wrap all CoreFun's in a CoreApp
        appRules (CoreFun x) = CoreApp (CoreFun x) []
        appRules (CoreApp x []) | not $ isCoreFun x = x
        appRules (CoreApp (CoreApp x y) z) = CoreApp x (y++z)
        appRules x = x

        hoApp = length [() | CoreApp x y <- universeExpr c2, not $ isCoreFun x]

        miss = [(x,d==GT)
               | CoreApp (CoreFun x) args <- universeExpr c2
               , Just a <- [Map.lookup x arity]
               , let d = compare (length args) a
               , d /= EQ]

        (over,under) = partition snd miss

        g = Set.size . Set.fromList . map fst

        pad x = replicate (8 - length s) ' ' ++ s
            where s = show x
