{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module DuplicateChecker where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad (filterM)
import Control.Monad.Reader (Reader,runReader,ask)
import Data.Default (def)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Language.Hasmtlib (Equatable(..),Boolean(..),and,or,false)
import qualified Language.Hasmtlib as SMT

import Utils.Type (Id(..))
import Utils.SMT (SMTSolver(..),Constraint,(<&&>),(<&&),smtVarMap)
import Typ.Type (Typ(..),Sort)
import Typ.Ops (flatten)
import Term.Type (Term(..),Head(..),FunTypMap)
import Equation.Type (Equation(..),ES)

type TypSkeletonFunsMap = Map Typ [Id]
type SMTIntExprMap = Map Id (SMT.Expr SMT.IntSort)

data DCProblem = DCProblem { file :: String
                           , sorts :: [Sort]
                           , funTypMap :: FunTypMap
                           , typSkeletonFunsMap :: TypSkeletonFunsMap
                           , equations :: ES
                           }

toSkeleton :: Typ -> Typ
toSkeleton (Typ as _) = Typ (map toSkeleton as) (Id "_")

toTypSkeletonFunsMap :: FunTypMap -> TypSkeletonFunsMap
toTypSkeletonFunsMap fTyM = M.fromListWith (++) vks where
  vks = map (\(f,a) -> (toSkeleton a, [f])) . M.toList $ fTyM

duplicates :: SMTSolver -> Bool -> [DCProblem] -> IO [(DCProblem,DCProblem)]
duplicates s debug ps = filterM (isDuplicate s debug) . duplicateCandidates $ ps

duplicateCandidates :: [DCProblem] -> [(DCProblem,DCProblem)]
duplicateCandidates ps =  let
  funsPerTypSkeleton x = map length . M.elems . typSkeletonFunsMap $ x
  in [ (x,y)
     | (i,x) <- zip [(0 :: Int)..] ps
     , (j,y) <- zip [0..] ps
     , i < j
     , (length . sorts $ x) == (length . sorts $ y)
     , (length . M.keys . funTypMap $ x) == (length . M.keys . funTypMap $ y)
     , (M.keys . typSkeletonFunsMap $ x) == (M.keys . typSkeletonFunsMap $ y)
     , funsPerTypSkeleton x == funsPerTypSkeleton y
     , (length . equations $ x) == (length . equations $ y)
     ]

isDuplicate :: SMTSolver -> Bool -> (DCProblem, DCProblem) -> IO Bool
isDuplicate (Solver _ s _) debug (x,y) = do
  (res,_) <- SMT.solveWith (if debug then SMT.solver (SMT.debugging def s) else SMT.solver s) $ do
    SMT.setLogic "ALL"
    let funsx = M.keys . funTypMap $ x
        funsy = M.keys . funTypMap $ y
        typSkeletons = M.keys . typSkeletonFunsMap $ x
    sx <- smtVarMap @SMT.IntSort (sorts x)
    sy <- smtVarMap @SMT.IntSort (sorts y)
    fx <- smtVarMap @SMT.IntSort funsx
    fy <- smtVarMap @SMT.IntSort funsy
    SMT.assert . SMT.distinct $ [sx M.! a | a <- sorts x]
    SMT.assert . SMT.distinct $ [sy M.! a | a <- sorts y]
    SMT.assert . SMT.distinct $ [fx M.! f | f <- funsx]
    SMT.assert . SMT.distinct $ [fy M.! f | f <- funsy]
    mapM_ SMT.assert [or [sx M.! a === sy M.! b | b <- sorts y] | a <- sorts x]
    -- TODO may generate false positives when first system contains variants
    mapM_ SMT.assert [or [ and $ (fx M.! f === fy M.! g) : [ sx M.! a === sy M.! b
                                                           | (a,b) <- zip (flatten fTyp) (flatten gTyp)
                                                           ]
                         | f <- (typSkeletonFunsMap x) M.! skel
                         , g <- (typSkeletonFunsMap y) M.! skel
                         , let fTyp = (funTypMap x) M.! f
                         , let gTyp = (funTypMap y) M.! g
                         ]
                     | skel <- typSkeletons
                     ]
    mapM_ SMT.assert [or [runReader (equationConstraint e e') (fx,fy) | e' <- equations y] | e <- equations x]
    return (sx,sy,fx,fy)
  case res of
    SMT.Sat -> return True
    SMT.Unsat -> return False
    SMT.Unknown -> error "impossible case"

equationConstraint :: Equation -> Equation -> Reader (SMTIntExprMap,SMTIntExprMap) Constraint
equationConstraint e e' = termConstraint (lhs e) (lhs e') <&&> termConstraint (rhs e) (rhs e')

termConstraint :: Term -> Term -> Reader (SMTIntExprMap,SMTIntExprMap) Constraint
termConstraint s t
  | nlams s == nlams t, length (sp s) == length (sp t) = case (hd s,hd t) of
      (F f,F g) -> do
        (sM,tM) <- ask
        ((sM M.! f) === (tM M.! g)) <&& recRes
      _ -> if hd s == hd t
        then recRes
        else return false
  | otherwise = return false
  where
    recRes = and <$> traverse (uncurry termConstraint) (zip (sp s) (sp t))




