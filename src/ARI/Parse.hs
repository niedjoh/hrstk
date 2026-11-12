{-# LANGUAGE OverloadedStrings #-}

-- |Parser for the hihger-order ARI format
module ARI.Parse (parser) where

import Control.Applicative (many,(<|>))
import Control.Monad (void)
import Control.Monad.Trans.State (gets,modify)
import Data.List (unsnoc)
import Data.Functor (($>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import qualified Data.Set as S
import Data.Text (Text)
import Fmt ((|+),(+|))
import Text.Megaparsec (choice,some,getOffset,setOffset)

import Utils.Misc (someIterations)
import Utils.ITerm (IEquation(..),ITerm(..),IHead(..),ipos,addFVTypes)
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

data Kind = SortDecl | FunDecl | Rule | Axiom | Conjecture

parser :: Parser [Maybe (Either IEquation IEquation)]
parser = do
  void $ format
  many sexpr

sexpr :: Parser (Maybe (Either IEquation IEquation))
sexpr = parensARI $ do
  k <- kind
  case k of
    SortDecl -> sortDecl $> Nothing
    FunDecl -> funDecl $> Nothing
    Rule -> Just . Left <$> equation True
    Axiom -> Just . Left <$> equation False
    Conjecture -> Just . Right <$> equation False

kind :: Parser Kind
kind = fromText <$> (   symbolARI "sort"
                    <|> symbolARI "fun"
                    <|> symbolARI "rule"
                    <|> symbolARI "axiom"
                    <|> symbolARI "conjecture"
                    ) where
  fromText "sort" = SortDecl
  fromText "fun" = FunDecl
  fromText "rule" = Rule
  fromText "axiom" = Axiom
  fromText "conjecture" = Conjecture
  fromText _ = error "impossible caes"

format :: Parser ()
format = parensARI $ do
  void $ symbolARI "format"
  void $ (symbolARI "higher-order" <|> symbolARI "HRS")

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

redefFun :: Text -> String
redefFun idt = "re-definition of function symbol '"+|idt|+"'"

redefVar :: Text -> String
redefVar idt = "re-definition of variable '"+|idt|+"'"

funDecl :: Parser ()
funDecl = do
  p <- getOffset
  fvM <- gets funVarMap
  idt <- identifierARI
  a <- typ
  case fvM M.!? idt of
    Just (Fun _) -> setOffset p >> fail (redefFun idt)
    Just (Var _) -> error "impossible case"
    Nothing -> modify $ insertFunVar idt (Fun a)

boundVarDecl :: Parser (Text,Typ)
boundVarDecl = parensARI $ do
  idt <- identifierARI
  a <- typ
  return (idt,a)

varDecl :: Map Text Typ -> Parser (Map Text Typ)
varDecl vM = parensARI $ do
  p <- getOffset
  fvM <- gets funVarMap
  idt <- identifierARI
  a <- typ
  case fvM M.!? idt of
    Just (Fun _) -> setOffset p >> fail (redefFun idt)
    Just (Var _) -> error "impossible case"
    Nothing -> case vM M.!? idt of
      Just _ -> setOffset p >> fail (redefVar idt)
      Nothing -> return $ M.insert idt a vM

freeVarsDecl :: Parser (Map Text Typ)
freeVarsDecl = do
  void $ symbolARI ":var"
  vM <- parensARI $ someIterations varDecl M.empty
  return vM

equation :: Bool -> Parser IEquation
equation b = do
  l <- term []
  r <- term []
  vM <- freeVarsDecl <|> pure M.empty
  return $ IEquation { ilhs = addFVTypes vM l
                     , irhs = addFVTypes vM r
                     , iisRule = b
                     , iposl = ipos l
                     , iposr = ipos r }

term :: Ctx -> Parser ITerm
term ctx = choice
  [ hdAsTerm ctx
  , parensARI $ choice [ lambda ctx
                       , appliedHd ctx]
  ]

hd :: Ctx -> Parser (IHead, Maybe Typ)
hd ctx = do
  idt <- identifierARI
  fvM <- gets funVarMap
  case lookup idt $ zipWith (\(k,v) i -> (k,(v,i))) ctx [0..] of
    Just (a,i) -> return (IDB (Id idt) i, Just a)
    Nothing    -> case fvM M.!? idt of
      Just (Fun a)  -> return (IF (Id idt), Just a)
      Just (Var _) -> error "impossible case"
      Nothing -> return (IFV (Named . Id $ idt), Nothing)

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
