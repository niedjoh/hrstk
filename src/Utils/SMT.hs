{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

-- |utility functions and abstractions for Hasmtlib
module Utils.SMT where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector (Vector)
import GHC.Generics
import qualified Language.Hasmtlib as SMT
import Language.Hasmtlib.Type.Solver (SolverConfig)

-- |type for SMT solvers
data SMTSolver = Solver String (SolverConfig SMT.SMT) (SolverConfig SMT.Pipe)

instance Show SMTSolver where
  show (Solver t _ _ ) = t

-- |newtype in order to avoid orphan instance of 'SMT.Codec'
newtype Vec a = Vec (Vector a) deriving (Functor, Foldable, Traversable, Generic)
instance SMT.Codec a => SMT.Codec (Vec a) where
  encode = fmap SMT.encode  
  decode sol = traverse (SMT.decode sol)

-- |SMTlib2 constraints (expressions of boolean type)
type IntExpr = SMT.Expr SMT.IntSort

-- |SMTlib2 constraints (expressions of boolean type)
type Constraint = SMT.Expr SMT.BoolSort

-- |vector containing 'IntExpr's
type VarVec = Vector (SMT.Expr SMT.IntSort)

-- |lifts '(&&)' into applicative context
(<&&>) :: Applicative f => f Constraint -> f Constraint -> f Constraint
(<&&>) = liftA2 (SMT.&&)

-- |A Version of '(&&)' where the second constraint is hidden in a functor.
(<&&) :: Functor f => Constraint -> f Constraint -> f Constraint
(<&&) x y = (SMT.&&) x <$> y

-- |lifts '(||)' into applicative context
(<||>) :: Applicative f => f Constraint -> f Constraint -> f Constraint
(<||>) = liftA2 (SMT.||)

-- |A Version of '(&&)' where the second constraint is hidden in a functor.
(<||) :: Functor f => Constraint -> f Constraint -> f Constraint
x <|| y = (SMT.||) x <$> y

infixr 3 <&&>, <&&
infixr 2 <||>, <||

-- |the SMT solver z3 <https://github.com/Z3Prover/z3>
z3 :: SMTSolver
z3 = Solver "z3" SMT.z3 SMT.z3

-- |the SMT solver cvc5 <https://cvc5.github.io/>
cvc5 :: SMTSolver
cvc5 = Solver "cvc5" SMT.cvc5 SMT.cvc5

-- |the SMT solver Yices2 <https://yices.csl.sri.com/>
yices :: SMTSolver
yices = Solver "yices" SMT.yices SMT.yices

-- |Takes a list of orderable elements and returns a map where each of these
-- elements is mapped to a fresh SMT variable of specified type.
smtVarMap :: (SMT.KnownSMTSort a, Ord k, SMT.MonadSMT s m) => [k] -> m (Map k (SMT.Expr a))
smtVarMap xs = M.fromList <$> mapM (\a -> (a,) <$> SMT.var) xs
