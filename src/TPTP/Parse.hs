{-# LANGUAGE OverloadedStrings #-}

-- |Parser for equational THF fragment.
module TPTP.Parse (parser) where

import Control.Applicative (many,(<|>))
import Control.Monad (void)
import Control.Monad.Trans.State (get,gets,put,modify)
import Data.Functor (($>))
import Data.List (unsnoc)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Fmt ((|+),(+|))
import Text.Megaparsec (choice,sepBy1,setOffset,getOffset)

import Utils.ITerm (IEquation(..),ITerm(..),IHead(..),ipos)
import Utils.Parse
    ( commaTPTP
    , dotTPTP
    , identifierStartingLowTPTP
    , identifierStartingUpTPTP
    , nameTPTP
    , parensTPTP
    , symbolTPTP
    , addSort
    , insertFunVar
    , Parser
    , Ctx
    , Env(..)
    , FunVar(..) )
import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..))

import Data.Text (Text)

data Role = Type | Axiom | Conjecture

-- |Parser for a fairly simple fragment of TPTP: simply-typed constant declarations together
-- with axioms/conjectures of the form ∀...∀ l = r
parser :: Parser [Maybe (Either IEquation IEquation)]
parser = many annotatedTHFFormula

annotatedTHFFormula :: Parser (Maybe (Either IEquation IEquation))
annotatedTHFFormula = do
  void $ symbolTPTP "thf"
  void $ symbolTPTP "("
  void nameTPTP
  void commaTPTP
  r <- role
  void commaTPTP
  mee <- case r of
    Type -> typeDecl $> Nothing
    Axiom -> Just . Left <$> equation
    Conjecture -> Just . Right <$> equation
  void $ symbolTPTP ")"
  void dotTPTP
  return mee

role :: Parser Role
role = fromText <$> (symbolTPTP "axiom" <|> symbolTPTP "type" <|> symbolTPTP "conjecture") where
  fromText "type" = Type
  fromText "axiom" = Axiom
  fromText "conjecture" = Conjecture
  fromText _ = error "impossible case"

typeDecl :: Parser ()
typeDecl = do
  p <- getOffset
  c <- identifierStartingLowTPTP
  void $ symbolTPTP ":"
  a <- (symbolTPTP "$tType" $> Nothing) <|> (Just . Fun <$> typ)
  case a of
    Just fv -> registerFunVar p c fv
    Nothing -> registerSort p c

registerSort :: Int -> Text -> Parser ()
registerSort p idt = do
  ss <- gets sorts
  if idt `S.member` ss
    then setOffset p >> fail ("re-definition of sort '"+|idt|+"'")
    else modify $ addSort idt

registerFunVar :: Int -> Text -> FunVar -> Parser ()
registerFunVar p idt fv = do
  fvM <- gets funVarMap
  case fvM M.!? idt of
    Just _ -> setOffset p >> fail ("re-definition of identifier '"+|idt|+"'")
    Nothing -> modify $ insertFunVar idt fv

typ :: Parser Typ
typ = do
  as <- sepBy1 parensTyp (symbolTPTP ">")
  case unsnoc as of
    Just (as',Typ as'' a) -> pure $ Typ (as' ++ as'') a
    _ -> error "impossible case"

parensTyp :: Parser Typ
parensTyp = choice
  [ sort
  , parensTPTP typ
  ]

sort :: Parser Typ
sort = do
  p <- getOffset
  a <- identifierStartingLowTPTP
  ss <- gets sorts
  if a `S.member` ss
    then return . Typ [] . Id $ a
    else setOffset p >> fail ("'"+|a|+"' is not a declared sort")

equation :: Parser IEquation
equation = do
  env <- get  
  e <- choice
    [ quantifierPrefix >> (parensTPTP termPair <|> termPair)
    , parensTPTP termPair
    , termPair
    ]
  put env -- modifications to environment are local to equation
  return e

quantifierPrefix :: Parser ()
quantifierPrefix = do
  void $ symbolTPTP "!"
  void $ symbolTPTP "["
  void $ sepBy1 varDecl (symbolTPTP ",")
  void $ symbolTPTP "]"
  void $ symbolTPTP ":"

varDecl :: Parser ()
varDecl = do
  p <- getOffset
  x <- identifierStartingUpTPTP
  void $ symbolTPTP ":"
  a <- typ
  registerFunVar p x (Var a)

boundVarDecl :: Parser (Text,Typ)
boundVarDecl = do
  x <- identifierStartingUpTPTP
  void $ symbolTPTP ":"
  a <- typ
  return (x,a)

termPair :: Parser IEquation
termPair = do
  l <- term []
  void $ symbolTPTP "="
  r <- term []
  return $ IEquation { ilhs = l, irhs = r, iisRule = False, iposl = ipos l, iposr = ipos r }

parensTerm :: Ctx -> Parser ITerm
parensTerm ctx = choice
  [ lam ctx
  , var ctx
  , fun
  , parensTPTP $ term ctx
  ]
  
term :: Ctx -> Parser ITerm
term ctx = do
  p <- getOffset
  ts <- sepBy1 (parensTerm ctx) (symbolTPTP "@")
  case ts of
    [s] -> return s
    IMat q ih a ss : us -> return $ IMat q ih a (ss ++ us)
    _:_ -> setOffset p >> fail "term is not in beta-normal form"
    [] -> error "impossible case"

lam :: Ctx -> Parser ITerm
lam ctx = do
  p <- getOffset
  void $ symbolTPTP "^"
  void $ symbolTPTP "["
  ps <- sepBy1 boundVarDecl (symbolTPTP ",")
  void $ symbolTPTP "]"
  void $ symbolTPTP ":"
  s <- term (reverse ps ++ ctx)
  return $ foldr (\(x,a) -> ILam p (Id x) a) s ps

var :: Ctx -> Parser ITerm
var ctx = do
  p <- getOffset
  x <- identifierStartingUpTPTP
  fvM <- gets funVarMap
  case lookup x $ zipWith (\(k,v) i -> (k,(v,i))) ctx [0..] of
    Just (a,i) -> return $ IMat p (IDB (Id x) i) (Just a) []
    Nothing -> case fvM M.!? x of
      Just (Var a) -> return $ IMat p (IFV (Named (Id x))) (Just a) []
      _ -> setOffset p >> fail ("'"+|x|+"' is not a declared variable")

fun :: Parser ITerm
fun = do
  p <- getOffset
  c <- identifierStartingLowTPTP
  fvM <- gets funVarMap
  case fvM M.!? c of
    Just (Fun a) -> return $ IMat p (IF (Id c)) (Just a) []
    _ -> setOffset p >> fail ("'"+|c|+"' is not a declared function symbol")
