{-# LANGUAGE OverloadedStrings #-}

-- |utility functions for input processing
module Utils.InputProcessing(InputType(..),processInput) where

import Data.Bifunctor (first, second)
import Data.List ((!?))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import Data.Void (Void)
import Prettyprinter (Pretty,Doc,(<+>),pretty,vsep)
import Text.Megaparsec (ParseError,ParseErrorBundle(..),errorBundlePretty)
import Text.Megaparsec.State (initialPosState)

import Utils.Type (Id(..),Var(..))
import Utils.ITerm (IEquation(..),ITerm(..),IHead(..),iTermToTerm,iEqToEq,isEtaExpandedIESBelowRoot,containsFunctionalIEq)
import Utils.Parse (Env(..),ProblemParser,constructErrorGeneric)
import qualified Utils.Parse as UP
import Utils.TypeInference (inferTypeIEq)
import Typ.Type (Typ(..),Sort)
import Term.Type (Term,FunTypMap)
import Term.Ops (isHeadedByFreeVar,isDHP,isPattern,secondOrder,linear)
import Equation.Type (ES)
import Equation.Ops (varCondition)

-- |type of input system
data InputType = ES | HRS | PRS | DPRS | DHPUnifProblem

instance Pretty InputType where
  pretty ES = "ES"
  pretty HRS = "HRS"
  pretty PRS = "PRS"
  pretty DPRS = "DPRS"
  pretty DHPUnifProblem = "DHP unification problem"

-- |Processes the input with consistent error handling
-- * parsing
-- * type inference
-- * input type check
processInput :: FilePath -> Text -> InputType -> Bool -> Bool -> Bool -> ProblemParser ->
  Either String (Int,[Sort],FunTypMap,Bool,Bool,ES,ES)
processInput file input inputType so ll pr parser = do
  (env,axs,conjs) <- first errorBundlePretty (parser file input)
  let (ss,fTyM) = processEnv env
  axsWithTyp <- mapM (prettyError . inferTypeIEq) axs
  conjs' <- mapM (prettyError . second fst . inferTypeIEq) conjs
  let (axs',n) = case inputType of
        DHPUnifProblem -> (map fst axsWithTyp,0)
        _ -> second maximum . unzip $ map pullDownToSort axsWithTyp
  axs'' <- mapM (prettyError . adjustToInputType inputType) axs'
  mapM_ (prettyError . restrict so secondOrder secondOrder constructSOError) axs''
  mapM_ (prettyError . restrict ll linear (const True) constructLinError) axs''
  mapM_ (prettyError . restrict pr isPattern (const True) constructPatError) axs''
  return (n, ss, fTyM, isEtaExpandedIESBelowRoot axs', containsFunctionalIEq (map fst axsWithTyp), map iEqToEq axs', map iEqToEq conjs') where
    iState = initialPosState file input
    toBundle pe = ParseErrorBundle { bundleErrors = pe :| [], bundlePosState = iState }
    prettyError = first (errorBundlePretty . toBundle)

-- |Convert the TextEntityMap used for parsing into a list of sorts as
-- well as a map from function symbols to types.
processEnv :: Env -> ([Sort], Map Id Typ)
processEnv env = (map Id . S.elems $ sorts env, M.mapKeysMonotonic Id m) where
  m = M.mapMaybe f (funVarMap env)
  f (UP.Fun a) = Just a
  f _ = Nothing

-- |Pulls down an equation to its corresponding return sort by applying it to fresh variables.
pullDownToSort :: (IEquation,Typ) -> (IEquation,Int)
pullDownToSort (ie,Typ as _) = (ie{ilhs = pdts $ ilhs ie, irhs = pdts $ irhs ie},n) where
  freshVars = [IMat undefined (IFV (Fresh i)) (Just a) []  | (a,i) <- zip as [0..]]
  n = length freshVars
  pdts (IMat p ih ma ts) = IMat p ih ma (ts++freshVars)
  pdts (ILam _ _ _ s) = accum 1 s
  accum i (ILam _ _ _ s) = accum (i+1) s
  accum i s@(IMat _ _ _ _) = let
    (bound,suffix) = first reverse $ splitAt i freshVars
    in case repl bound s of
      IMat p ih ma ts -> IMat p ih ma (ts++suffix)
      _ -> error "impossible case"
  repl bound (IMat p ih ma ts)
    | IDB _ i <- ih, Just (IMat _ v _ _) <- bound !? i = IMat p v ma (map (repl bound) ts)
    | otherwise = IMat p ih ma (map (repl bound) ts)
  repl bound (ILam p idt a s) = ILam p idt a (repl bound s)

-- |Checks whether an equation adheres to the mandated input type and determines whether it should
-- be a rule or equation
adjustToInputType :: InputType -> IEquation -> Either (ParseError Text Void) IEquation
adjustToInputType ES ie = Right ie
adjustToInputType HRS ie
  | isHeadedByFreeVar . iTermToTerm . ilhs $ ie =
      Left $ constructITError HRS (iposl ie) "free variable in head position of left-hand side"
  | not . varCondition . iEqToEq $ ie =
      Left $ constructITError HRS (iposr ie) "extra variables on right-hand side"
  | otherwise = Right $ ie{iisRule = True}
adjustToInputType PRS ie
  | not . isPattern . iTermToTerm . ilhs $ ie =
      Left $ constructITError PRS (iposl ie)
      "left-hand side is not a pattern"
  | otherwise = Right ie
adjustToInputType DPRS ie
  | not . isDHP . iTermToTerm . ilhs $ ie =
      Left $ constructITError DPRS (iposl ie)
      "left-hand side is not a deterministic higher-order pattern" 
  | otherwise = adjustToInputType HRS ie
adjustToInputType DHPUnifProblem ie
  | not . isDHP . iTermToTerm . ilhs $ ie =
      Left $ constructITError DHPUnifProblem (iposl ie)
      "left-hand side is not a deterministic higher-order pattern"
  | not . isDHP . iTermToTerm . irhs $ ie =
      Left $ constructITError DHPUnifProblem (iposr ie)
      "right-hand side is not a deterministic higher-order pattern"
  | otherwise =  Right ie

-- |Checks whether an equation satisfies a specified restriction
restrict :: Bool -> (Term -> Bool) -> (Term -> Bool) -> (Int -> ParseError Text Void) ->
  IEquation -> Either (ParseError Text Void) IEquation
restrict False _ _ _ ie = Right ie
restrict True lRestr rRestr err ie
  | not . lRestr . iTermToTerm . ilhs $ ie = Left $ err (iposl ie)
  | not . rRestr . iTermToTerm . irhs $ ie = Left $ err (iposr ie)
  | otherwise = Right ie

-- |Construct a input type error.
constructITError :: InputType -> Int -> Doc ann -> ParseError Text Void
constructITError inputType i d = constructErrorGeneric i doc where
  doc = vsep ["not a valid" <+> pretty inputType <+> "rule",d]

-- |Helper function to construct "not of second-order" error which looks like a parse
-- error and points to the corresponding position in the input.
constructSOError :: Int -> ParseError Text Void
constructSOError i = constructErrorGeneric i "not a second-order term"

-- |Helper function to construct "not linear" error which looks like a parse
-- error and points to the corresponding position in the input.
constructLinError :: Int -> ParseError Text Void
constructLinError i = constructErrorGeneric i "not a linear term"

-- |Helper function to construct "not pattern" error which looks like a parse
-- error and points to the corresponding position in the input.
constructPatError :: Int -> ParseError Text Void
constructPatError i = constructErrorGeneric i "not a pattern"
