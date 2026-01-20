{-# LANGUAGE OverloadedStrings #-}

-- |Parser for the hihger-order ARI format
module ARI.Parse (parser) where

import Control.Applicative (many,(<|>))
import Control.Monad (void)
import Control.Monad.Trans.State (gets,modify)
import Data.List (unsnoc)
import Data.Functor (($>))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import Fmt ((|+),(+|))
import Text.Megaparsec (choice,some,getOffset,setOffset)

import Utils.ITerm (IEquation(..),ITerm(..),IHead(..),ipos)
import Utils.Parse
    ( identifierARI
    , parensARI
    , symbolARI
    , Parser
    , Ctx
    , FunVar(..)
    , Env(..)
    , addSort
    , insertFunVar
    )
import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..))


data Kind = SortDecl | FunDecl | VarDecl | Rule | Axiom | Conjecture

parser :: Parser [Maybe (Either IEquation IEquation)]
parser = do
  void $ format
  many sexpr

sexpr :: Parser (Maybe (Either IEquation IEquation))
sexpr = parensARI $ do
  k <- kind
  case k of
    SortDecl -> sortDecl $> Nothing
    FunDecl -> funVarDecl Fun $> Nothing
    VarDecl -> funVarDecl Var $> Nothing
    Rule -> Just . Left <$> equation True
    Axiom -> Just . Left <$> equation False
    Conjecture -> Just . Right <$> equation False

kind :: Parser Kind
kind = fromText <$> (   symbolARI "sort"
                    <|> symbolARI "fun"
                    <|> symbolARI "var"
                    <|> symbolARI "rule"
                    <|> symbolARI "axiom"
                    <|> symbolARI "conjecture"
                    ) where
  fromText "sort" = SortDecl
  fromText "fun" = FunDecl
  fromText "var" = VarDecl
  fromText "rule" = Rule
  fromText "axiom" = Axiom
  fromText "conjecture" = Conjecture
  fromText _ = error "impossible caes"

format :: Parser ()
format = parensARI $ do
  void $ symbolARI "format"
  void $ symbolARI "higher-order"

sortDecl ::Parser ()
sortDecl = do
  p <- getOffset
  ss <- gets sorts
  idt <- identifierARI
  if idt `S.member` ss
    then setOffset p >> fail ("re-definition of sort '"+|idt|+"'")
    else modify $ addSort idt

sort :: Parser Typ
sort = do
  p <- getOffset
  idt <- identifierARI
  ss <- gets sorts
  if idt `S.member` ss
    then return . Typ [] . Id $ idt
    else setOffset p >> fail ("'"+|idt|+"' is not a declared sort")

arrowTyp :: Parser Typ
arrowTyp = parensARI $ do
  p <- getOffset
  void $ symbolARI "->"
  as <- some typ
  case unsnoc as of
    Just (bs@(_:_),Typ [] b) -> return $ Typ bs b
    Just ([],_) -> setOffset p >> fail "not a valid type expression"
    Just (_,Typ (_:_) _) -> setOffset p >> fail "the final argument of -> should be a sort"
    Nothing -> error "impossible case"

typ :: Parser Typ
typ = choice
  [ sort
  , arrowTyp
  ]

funVarDecl :: (Typ -> FunVar) -> Parser ()
funVarDecl f = do
  p <- getOffset
  fvM <- gets funVarMap
  idt <- identifierARI
  a <- typ
  case fvM M.!? idt of
    Just _ -> setOffset p >> fail ("re-definition of function/variable '"+|idt|+"'")
    Nothing -> modify $ insertFunVar idt (f a)

equation :: Bool -> Parser IEquation
equation b = do
  l <- term []
  r <- term []
  return $ IEquation { ilhs = l, irhs = r, iisRule = b, iposl = ipos l, iposr = ipos r}

term :: Ctx -> Parser ITerm
term ctx = choice
  [ hdAsTerm ctx
  , parensARI $ choice [ lambda ctx
                       , appliedHd ctx]
  ]

boundVarDecl :: Parser (Text,Typ)
boundVarDecl = parensARI $ do
  idt <- identifierARI
  a <- typ
  return (idt,a)

hd :: Ctx -> Parser (IHead, Maybe Typ)
hd ctx = do
  idt <- identifierARI
  fvM <- gets funVarMap
  case lookup idt $ zipWith (\(k,v) i -> (k,(v,i))) ctx [0..] of
    Just (a,i) -> return (IDB (Id idt) i, Just a)
    Nothing -> case fvM M.!? idt of
      Just (Fun a) -> return (IF (Id idt), Just a)
      Just (Var a) -> return (IFV (Named . Id $ idt), Just a)
      _ -> return (IFV (Named . Id $ idt), Nothing)

hdAsTerm :: Ctx -> Parser ITerm
hdAsTerm ctx = do
  p <- getOffset
  (ih,ma) <- hd ctx
  return $ IMat p ih ma []

lambda :: Ctx -> Parser ITerm
lambda ctx = do
  p <- getOffset
  void $ symbolARI "lambda"
  ps <- parensARI $ some boundVarDecl
  s <- term (reverse ps ++ ctx)
  return $ foldr (\(x,a) -> ILam p (Id x) a) s ps

appliedHd :: Ctx -> Parser ITerm
appliedHd ctx = do
  p <- getOffset
  (ih,ma) <- hd ctx
  ts <- many (term ctx)
  return $ IMat p ih ma ts
