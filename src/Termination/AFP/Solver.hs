{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Termination.AFP.Solver where

import qualified Language.Hasmtlib as SMT
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Utils.Type
import Typ.Ops
import Term.Ops
import Typ.Type
import Term.Type
import Utils.SMT (SMTSolver(Solver),z3,cvc5,yices, Constraint, IntExpr, smtVarMap)
import Equation.Type
import Equation.Ops

data AFPInfo = AFPInfo
  { sPrec :: M.Map Id IntExpr -- Maps each Sort (Id) to an SMT integer weight
  }

geSort :: AFPInfo -> Id -> Id -> Constraint
geSort env iota kappa = (sPrec env M.! iota) SMT.>=? (sPrec env M.! kappa)

gtSort :: AFPInfo -> Id -> Id -> Constraint
gtSort env iota kappa = (sPrec env M.! iota) SMT.>? (sPrec env M.! kappa)

-- The top-level solver execution
checkAFP :: SMTSolver -> [Sort] -> ES -> IO Bool
checkAFP (Solver _ s _) allSorts hrs
 -- TODO: Change when we have better definition
 | not ((all patternRule hrs)) = return False
 | otherwise = do
  (res, _) <- SMT.solveWith (SMT.solver s) $ do
    -- 1. Initialize variables for every sort
    sortPrecedence <- smtVarMap @SMT.IntSort allSorts
    let env = AFPInfo { sPrec = sortPrecedence }
    
    -- 2. Build the global constraint for all rules
    let globalConstraints = map (afpRule env) hrs
    
    -- 3. Assert them simultaneously
    mapM_ SMT.assert globalConstraints
    
  return (res == SMT.Sat)


afpRule :: AFPInfo -> Equation -> Constraint
afpRule env (Equation {lhs = l, rhs = r}) = 
    let 
        zs = Set.toList (freeVars r) 
        lhsArgs = sp l
        
        -- Generates the existential constraint for a single Z
        constraintForZ :: Var -> Constraint
        constraintForZ z = 
            let 
                -- Find every instance of t inside every l_i where hd(t) == Z
                validTargets = [ (li, t) | li <- lhsArgs
                                         , t  <- findSubtermsWithHead (FV z) li ]
                
                -- Generate the accessibility condition for each potential target
                accessibilityChecks = map (\(li, t) -> accessibleArguments env li t) validTargets
            in 
                if null accessibilityChecks 
                then SMT.false
                else SMT.or accessibilityChecks
                
    in 
        if null zs 
        then SMT.true 
        else SMT.and (map constraintForZ zs)

-- Term has the form Term { nlams :: Int, hd :: Head, sp :: [Term], typ :: Typ
accessibleArguments :: AFPInfo -> Term -> Term -> Constraint
accessibleArguments env term@(Term {nlams = n, hd = h, sp = s, typ = ty}) t
    | term == t = SMT.true
    | n > 0     = accessibleArguments env (term { nlams = n - 1, typ = getBodyType ty }) t
    | isFV h || isFun h = 
        let hdTyp = getHeadType term
            subs  = accSMT env h hdTyp
            
            -- Map the 1-based index 'i' to the 0-based spine 's', checking free variables
            validSubs = [ (s !! (i-1), accCond) 
                        | (i, accCond) <- subs
                        , case h of
                            FV v -> v `Set.notMember` freeVars (s !! (i-1))
                            _    -> True 
                        ]
            
            -- If the argument's sort constraint holds AND the recursive check holds, it's valid
            subConstraints = map (\(sub, cond) -> cond SMT.&& accessibleArguments env sub t) validSubs
        in SMT.or subConstraints
    | otherwise = SMT.false
        

accSMT :: AFPInfo -> Head -> Typ -> [(Int, Constraint)]
accSMT env headSymbol headTyp = case headSymbol of
    F _  -> [ (i, succEqPlus env iota sigma)            | (sigma, i) <- zip sigmas [1..] ]
    FV _ -> [ (i, succEqPlus env iota (returnTyp sigma)) | (sigma, i) <- zip sigmas [1..] ]
  where 
    sigmas = argTyps headTyp
    iota   = returnSort headTyp

succEqPlus :: AFPInfo -> Id -> Typ -> Constraint
succEqPlus env iota sigma = 
    geSort env iota kappa SMT.&& SMT.and (map (succMinus env iota) sigmas)
  where
    kappa  = returnSort sigma
    sigmas = argTyps sigma

succMinus :: AFPInfo -> Id -> Typ -> Constraint
succMinus env iota sigma = 
    gtSort env iota kappa SMT.&& SMT.and (map (succEqPlus env iota) sigmas)
  where
    kappa  = returnSort sigma
    sigmas = argTyps sigma


getBodyType :: Typ -> Typ
getBodyType (Typ (_:args) baseSort) = Typ args baseSort
getBodyType (Typ [] _) = error "Cannot strip lambda: no argument types left"


getHeadType :: Term -> Typ
getHeadType term =
  let spineTyps    = map typ (sp term)
      remainingArgs = drop (nlams term) (argTyps (typ term))
      baseSort      = returnSort (typ term)
      bodyTyp       = Typ remainingArgs baseSort
  in liftTyp spineTyps bodyTyp


-- Recursively finds all subterms within a term that are headed by the target Z
findSubtermsWithHead :: Head -> Term -> [Term]
findSubtermsWithHead z term@(Term {hd = h, sp = spine}) = 
    let current  = if h == z then [term] else []
        children = concatMap (findSubtermsWithHead z) spine
    in current ++ children