{-# LANGUAGE OverloadedStrings #-}
module Main where

import Ari
import System.IO (hPutStrLn)
import Control.Monad (forM_)
import Options.Applicative
import System.Directory (doesDirectoryExist)



main :: IO ()
main = do
    opts <- execParser (info (optsP <**> helper) 
        (fullDesc 
        <> progDesc "transform higher-order ARI files representing EPRSs to well-behaved presentation"
        <> header "hrstk-wb-transformer"))
    let inFile = inputFile opts
    putStrLn $ "Scanning directory: " ++ inFile
    files <- getAriFiles inFile
    isDir <- doesDirectoryExist inFile
    putStrLn $ "Found " ++ show (length files) ++ " .ari files. Starting batch job..."
    
    withLogHandle (logFile opts) $ \h -> do    
        hPutStrLn h $ "--- Starting Batch Job for " ++ inFile ++ " ---"
        hPutStrLn h $ "Found " ++ show (length files) ++ " files."
        forM_ files (processAriFile h inFile opts isDir)
        hPutStrLn h "--- Batch Job Complete ---"
    
    putStrLn "Batch processing complete! Check batch_results.log for details."