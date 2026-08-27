{-# LANGUAGE OverloadedStrings #-}
module Main where

import System.Environment (getArgs)
import Ari
import System.IO (withFile, IOMode(..), hPutStrLn)
import Control.Monad (forM_)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [targetDir] -> do
            -- We can still print basic progress to the console so you aren't staring at a blank screen
            putStrLn $ "Scanning directory: " ++ targetDir
            files <- getAriFiles targetDir
            putStrLn $ "Found " ++ show (length files) ++ " .ari files. Starting batch job..."
            
            -- Open "batch_results.log" in WriteMode (overwrites) or AppendMode (adds to the end)
            withFile "batch_results.log" WriteMode $ \h -> do
                
                hPutStrLn h $ "--- Starting Batch Job for " ++ targetDir ++ " ---"
                hPutStrLn h $ "Found " ++ show (length files) ++ " files."
                
                -- Process every file, passing the handle 'h' to the function
                forM_ files (processAriFile h targetDir)
                
                hPutStrLn h "--- Batch Job Complete ---"
            
            putStrLn "Batch processing complete! Check batch_results.log for details."
            
        _ -> putStrLn "Usage: cabal run <absolute directory_path>"