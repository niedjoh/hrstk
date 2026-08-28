{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (replicateM)
import Data.Char (toLower)
import Hedgehog (Gen, Size(..))
import qualified Hedgehog.Gen as G
import Options.Applicative
    ( (<**>),
      argument,
      eitherReader,
      fullDesc,
      header,
      help,
      info,
      long,
      metavar,
      option,
      progDesc,
      short,
      showDefault,
      str,
      switch,
      value,
      execParser,
      helper,
      Parser,
      ParserInfo )
import Prettyprinter (Pretty,pretty,vsep)
import Prettyprinter.Render.Text (putDoc)
import Text.Read (readEither)

import Utils.Type (Id)
import Typ.Type (Typ)
import Typ.Ops (returnSort)
import Gen (AvailMap,typClosure,availMap,genTyp,genArbitraryTerm,genDHP)

data Args = Args
  { size :: Size
  , n :: Int
  , dhp :: Bool
  }

main :: IO ()
main = do
  args <- execParser opts
  if dhp args
    then printDHPSamples (size args) (n args)
    else printTermSamples (size args) (n args)

printSamples :: Pretty a => ([Typ] -> AvailMap -> Id -> Gen a) -> Int -> IO ()
printSamples gen i = do
  a <- G.sample genTyp
  let as = typClosure a
  let availM = availMap as
  ps <- replicateM i $ G.sample $ gen as availM (returnSort a)
  putDoc (vsep . map pretty $ ps)
  putStrLn ""

printTermSamples :: Size -> Int -> IO ()
printTermSamples size = printSamples (\as availM a -> G.resize size $ genArbitraryTerm as availM a)

printDHPSamples :: Size -> Int -> IO ()
printDHPSamples size = printSamples (\as availM a -> G.resize size $ genDHP as availM a)

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc "generates random terms"
  <> header "hrstk-gen - higher-order term generator" )

argsParser :: Parser Args
argsParser = Args
  <$> option (eitherReader (\s -> Size <$> restrIntFromString (\i -> 0 <= i && i <= 100) s))
      ( long "size"
     <> short 's'
     <> showDefault
     <> value 50
     <> metavar "0 <= i <= 100"
     <> help "size of generated terms" )
  <*> option (eitherReader $ restrIntFromString (>= 1))
      ( long "number"
     <> short 'n'
     <> showDefault
     <> value 1
     <> metavar "1 <= i"
     <> help "number of generated terms" )
  <*> switch
      ( long "dhp"
     <> short 'd'
     <> help "only generate DHPs" )

restrIntFromString :: (Int -> Bool) -> String -> Either String Int
restrIntFromString f s = do
  i <- readEither s
  if f i
    then Right i
    else Left "not in range"
