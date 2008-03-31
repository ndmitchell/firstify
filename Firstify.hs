
module Main(main) where

import Control.Arrow
import Control.Monad
import Data.List
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.CPUTime
import System.IO
import Yhc.Core
import Yhc.Core.Firstify
import Yhc.Core.Firstify.Paper
import Yhc.Core.Firstify.MitchellOld
import qualified Data.Map as Map


data Actions = Reynolds | Mitchell | Super | Stats | Help | MitchellOld | Paper | Normalise | CPU
             | Output String | MainIs CoreFuncName | OutCore | Text | Html | Verbose | Log
             deriving (Show,Eq)


opts =
    [Option "r" ["reynolds"] (NoArg Reynolds) "Perform Reynolds defunctionalisation"
    ,Option "m" ["mitchell"] (NoArg Mitchell) "Perform Mitchell defunctionalisation"
    ,Option "s" ["super"]    (NoArg Super)    "Perform Super defunctionalisation"
    ,Option "p" ["paper"]    (NoArg Paper)    "Perform paper style defunctionalisation"
    ,Option "M" []           (NoArg MitchellOld) "Debugging option (to be removed)"
    ,Option "i" ["info"]     (NoArg Stats   ) "Show additional statistics"
    ,Option "v" ["verbose"]  (NoArg Verbose ) "Give verbose statistics"
    ,Option "n" ["normal"]   (NoArg Normalise) "Normalise the result by basic inlining"
    ,Option "l" ["log"]      (NoArg Log     ) "Log all final results and statistics"
    ,Option "o" []     (ReqArg Output "file") "Where to put the output file"
    ,Option "c" ["core"]     (NoArg OutCore ) "Output a Core file"
    ,Option "t" ["text"]     (NoArg Text    ) "Output a text file of the Core"
    ,Option "h" ["html"]     (NoArg Html    ) "Output an HTML file of the Core"
    ,Option "?" ["help"]     (NoArg Help    ) "Show help message"
    ,Option "x" ["cpu"]      (NoArg CPU     ) "CPU Time"
    ,Option ""  ["main"] (ReqArg MainIs "function") "Function to use instead of main"
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

    let newmain = [name | MainIs name <- acts]
    c <- return $ if null newmain then c else replaceMain c (head newmain)

    let verbose = Verbose `elem` acts
        stats c = do
            when (Stats `elem` acts) $ do
                let msg = showStats verbose c
                length msg `seq` putStr msg
                hFlush stdout
            return c
    stats c
    
    tBegin <- getCPUTime

    c <- if Mitchell `notElem` acts then return c else do
        putStrLn "Performing Mitchell firstification"
        stats $ (if MitchellOld `elem` acts then mitchellOld else mitchell) c

    c <- if Paper `notElem` acts then return c else do
        putStrLn "Performing Paper firstification"
        stats $ paper c

    c <- if Super `notElem` acts then return c else do
        putStrLn "Performing Super firstification"
        stats $ super c

    c <- if Reynolds `notElem` acts then return c else do
        putStrLn "Performing Reynold's firstification"
        stats $ reynolds c

    tEnd <- getCPUTime
    when (CPU `elem` acts) $ putStrLn $ "Time taken: " ++ showCPUTime (tEnd - tBegin)

    let ext = ['m' | Mitchell `elem` acts] ++ ['r' | Reynolds `elem` acts] ++
              ['s' | Super `elem` acts] ++ ['p' | Paper `elem` acts]
    out <- case [o | Output o <- acts] of
               o:_ -> return o
               _ -> findOutput (if null ext then "none" else ext) $ head files

    when (Log `elem` acts) $
        appendFile "log.txt" $ unlines [unwords args, showStats False c]

    c <- return $ if Normalise `notElem` acts then c else
                  coreReachable ["main"] $ coreInline InlineForward c

    putStrLn "Writing result"
    when (OutCore `elem` acts) $ saveCore out c
    when (Text `elem` acts) $ writeFile (out <.> "txt") (show c)
    when (Html `elem` acts) $ writeFile (out <.> "htm") (coreHtml c)



showCPUTime :: Integer -> String
showCPUTime x = show (x `div` 1000000000) ++ "ms"

-- figure out where a file should go if we don't get an output location
findOutput ext s = return $ replaceBaseName s (takeBaseName s <.> ext)


replaceMain c name = coreReachable ["main"] c{coreFuncs = concatMap f $ coreFuncs c}
    where
        f x | name `isSuffixOf` n = [x{coreFuncName="main"}]
            | otherwise = [x | n /= "main"]
            where n = coreFuncName x


{- statistics:
    HO Applications:
        The number of times you apply arguments to a non
        function or constructor, i.e. CoreApp v14 [v15]
        Verbose: which functions they occur within
    Lambdas:
        The number of CoreLam expressions
        Verbose: which functions they occur within
    Under-Sat calls:
        The number of applictions without enough arguments, i.e.
        map f, where f has arity 2
        Verbose: which functions they occur within
    Under-Sat funs:
        The number of functions called without enough arguments
        i.e. map lacks 1 argument
        Verbose: which functions they are
    Over-Sat: reverse of under-sat
-}
showStats :: Bool -> Core -> String
showStats verbose c = unlines $
        "Higher-Order Statistics" :
        [sa ++ replicate (25 - length sa - length sb) ' ' ++ sb ++ verb c
            | (sa,(b,c)) <- res, let sb = show b] ++
        [if lambCount == 0 then "success" else "FAILURE"] ++
        ["Summary" ++ concat ["\t" ++ show b | (i,(_,(b,_))) <- zip [0..] res, i `notElem` [3,5]] | verbose]
    where
        res = let (*) = (,) in
            ["HO Applications"  * show1 hoApp
            ,"Lambdas"          * show1 lamb
            ,"Under-Sat calls"  * show2 under
            ,"Under-Sat funs"   * show3 under
            ,"Over -Sat calls"  * show2 over
            ,"Over -Sat funs"   * show3 over
            ,"Functions"        * (length $ coreFuncs c3, [])
            ,"Nodes"            * (length $ universeExpr c3, [])
            ]

        verb info = if verbose && not (null res) then "\n    " ++ unwords res else ""
            where res = [a ++ "=" ++ show b | (a,b) <- info, b /= 0]


        -- PREPARTION
        uni = [(name, universe body) | CoreFunc name _ body <- coreFuncs c2]
        arity = Map.fromList [(coreFuncName x, coreFuncArity x) | x <- coreFuncs c2]

        c2 = transformExpr appRules c
        c3 = coreReachable ["main"] $ coreInline InlineForward c2

        -- use all the CoreApp properties
        -- plus wrap all CoreFun's in a CoreApp
        appRules (CoreFun x) = CoreApp (CoreFun x) []
        appRules (CoreApp x []) | not $ isCoreFun x = x
        appRules (CoreApp (CoreApp x y) z) = CoreApp x (y++z)
        appRules x = x


        -- FIRST TWO
        hoApp = [(name,length $ filter isHOApp inner) | (name,inner) <- uni]
            where
                isHOApp (CoreApp x y) = not $ isCoreCon x || isCoreFun x
                isHOApp _ = False

        lamb = [(name, length $ filter isCoreLam inner) | (name,inner) <- uni]
        lambCount = sum $ map snd lamb

        show1 xs = (sum $ map snd xs, xs)


        -- SECOND TWO

        (over,under) = partition fst
               [(d==GT, (name,fun))
               | (name,inner) <- uni
               , CoreApp (CoreFun fun) args <- inner
               , Just a <- [Map.lookup fun arity]
               , let d = compare (length args) a, d /= EQ]

        show2 set = (length set, show4 fst set)
        show3 set = (length . group . sort . map (fst . snd) $ set, show4 snd set)

        show4 pick = map (head &&& length) . group . sort . map (pick . snd)
