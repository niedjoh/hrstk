{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

-- |utility functions for parsing. By convention, each parser automatically consumes trailing space.
module Utils.Parse where

import Control.Applicative ((<|>))
import Control.Monad.Trans.State (StateT,runStateT)
import Data.Char (isDigit,isAlphaNum,isPrint,isSpace)
import Data.Either (partitionEithers)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Prettyprinter (Doc)
import Text.Megaparsec ( MonadParsec
                       , Parsec
                       , Token
                       , Tokens
                       , ParseErrorBundle(..)
                       , ParseError
                       , between
                       , satisfy
                       , takeWhileP
                       , takeWhile1P
                       , parse
                       , empty )
import Text.Megaparsec.Char (space1,lowerChar,upperChar,letterChar)
import Text.Megaparsec.Error (ErrorFancy(..))
import Text.Megaparsec.Error.Builder (errFancy,fancy)
import qualified Text.Megaparsec.Char.Lexer as L

import Utils.ITerm (IES,IEquation)
import Utils.Pretty (docToString)
import Typ.Type (Typ)

data FunVar = Fun Typ | Var Typ deriving Eq

data Env = Env { funVarMap :: Map Text FunVar
               , sorts :: Set Text
               }

type Ctx = [(Text,Typ)]

-- |MegaParsec parser using 'Text' with Env
type Parser = StateT Env (Parsec Void Text)

-- |type of a general problem parsing function
type ProblemParser = FilePath -> Text -> Either (ParseErrorBundle Text Void) (Env, IES, IES)

emptyEnv :: Env
emptyEnv = Env { sorts = S.empty, funVarMap = M.empty}

-- |Adds a sort to the set in the environment
addSort :: Text -> Env -> Env
addSort a env = env{sorts = S.insert a $ sorts env}

-- |Updates the mapping of identifiers to Fun/Var + type of the environment
insertFunVar :: Text -> FunVar -> Env -> Env
insertFunVar idt fv env = env{funVarMap = M.insert idt fv $ funVarMap env}

-- |Generic problem parser
parseProblem :: Parser () -> Parser [Maybe (Either IEquation IEquation)] -> ProblemParser
parseProblem sc parser file input = case parse (runStateT (sc >> parser) emptyEnv) file input of
  Right (mees,env) -> Right (env,axs,conjs) where
    (axs,conjs) = partitionEithers . catMaybes $ mees
  Left bundle -> Left bundle

-- |Helper function to generate an error message which looks like a parse error and
-- points to the corresponding position in the input
constructErrorGeneric :: Int -> Doc ann -> ParseError Text Void
constructErrorGeneric i s = errFancy i (fancy . ErrorFail . docToString $ s)

-- |Checks whether a given 'Char' is alphanumeric or an underscore.
isAlphaNumU :: Char -> Bool
isAlphaNumU c = isAlphaNum c || c == '_'

isAllowedARI :: Char -> Bool
isAllowedARI c = isPrint c && not (isSpace c) && (not $ c `elem` ['(',')',';',':'])

-- |consumes trailing space and ignores comments
scTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m ()
scTPTP = L.space space1 (L.skipLineComment "%") (L.skipBlockComment "/*" "*/")

-- |consumes trailing space and ignores comments
scARI :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m ()
scARI = L.space space1 (L.skipLineComment ";") empty

-- |A parser for strings containing letters, underscores and digits starting with a letter.
identifierTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
identifierTPTP =
  lexemeTPTP $ T.cons <$> letterChar <*> takeWhileP (Just "alpha, num or underscore char") isAlphaNumU

-- |A parser for strings containing letters, underscores and digits starting with a letter.
identifierARI :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
identifierARI =
  lexemeARI $ takeWhile1P (Just "printable unicode character except ␣ \\t \\n ( ) ; :") isAllowedARI

-- |A parser for names which are numbers or identifiers starting with a letter.
nameTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
nameTPTP = lexemeTPTP $ identifierTPTP <|> numberTPTP

-- |A parser for names starting with lowercase letters which are numbers or
-- identifiers starting with lowercase letters.
nameStartingLowTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
nameStartingLowTPTP = lexemeTPTP (identifierStartingLowTPTP <|> numberTPTP)

-- |A parser for strings containing letters, underscores and digits starting with a lowercase letter.
identifierStartingLowTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
identifierStartingLowTPTP =
  lexemeTPTP (T.cons <$> lowerChar <*> takeWhileP (Just "alpha, num or underscore char") isAlphaNumU)

-- |A parser for names starting with lowercase letters which are numbers or
-- identifiers starting with uppercase letters.
nameStartingUpTPTP ::(MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
nameStartingUpTPTP = lexemeTPTP (identifierStartingUpTPTP <|> numberTPTP)

-- |A parser for strings containing letters, underscores and digits starting with an uppercase letter.
identifierStartingUpTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
identifierStartingUpTPTP =
  lexemeTPTP (T.cons <$> upperChar <*> takeWhileP (Just "alpha, num or underscore char") isAlphaNumU)

-- |A parser for numbers with no leading zeroes.
numberTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
numberTPTP = lexemeTPTP (T.cons <$> nonZeroNumber <*> takeWhileP (Just "num") isDigit) where
  nonZeroNumber = satisfy (\c -> isDigit c && c /= '0')

-- |A parser for the dot symbol.
dotTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
dotTPTP = symbolTPTP "."

-- |A parser for the comma symbol.
commaTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m Text
commaTPTP = symbolTPTP ","

-- |Modifies a parser to operate between parentheses.
parensTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m a -> m a
parensTPTP = lexemeTPTP . between (symbolTPTP "(") (symbolTPTP ")")

-- |Modifies a parser to operate between parentheses.
parensARI :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m a -> m a
parensARI = lexemeARI . between (symbolARI "(") (symbolARI ")")

-- |Modifies a given parser to also consume trailing space.
lexemeTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m a -> m a
lexemeTPTP = L.lexeme scTPTP

-- |Modifies a given parser to also consume trailing space.
lexemeARI :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => m a -> m a
lexemeARI = L.lexeme scARI

-- |A parser for a given symbol which consumes trailing space.
symbolTPTP :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => Text -> m Text
symbolTPTP = L.symbol scTPTP

-- |A parser for a given symbol which consumes trailing space.
symbolARI :: (MonadParsec e s m, Token s ~ Char, Tokens s ~ Text) => Text -> m Text
symbolARI = L.symbol scARI
