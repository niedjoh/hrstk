module WellBehaved where

import Term.Type
import Utils.Type
import Typ.Ops(sort)

data Symbol = SymFunc Id 
            | SymVar Var
            deriving (Show, Eq)

-- Computes the list of Free Variables of a Term
freeVariablesLHS :: Term -> [Head]
freeVariablesLHS term = case hd term of
    FV x -> FV x : concatMap freeVariablesLHS (sp term)
    _    -> concatMap freeVariablesLHS (sp term)

-- Computes the arities of all the function symbols
getArities :: Term -> [(Head,Int)]
getArities term = case hd term of
    FV x -> (FV x, length $ sp term) : concatMap getArities (sp term)
    F f -> (F f, length $ sp term) : concatMap getArities (sp term)
    _ ->  concatMap getArities (sp term)

-- Check if the airity of a function symbol is consistant through the whole term
checkArityConsitency :: [(Head,Int)] -> Bool
checkArityConsitency [] = True
checkArityConsitency ((h,i):xs) = all (\(_,i') -> i' == i) dups && checkArityConsitency rest
 where dups = filter (\(h',_) -> h == h') xs
       rest = filter (\(h',_) -> h /= h') xs


-- Check if a SMTRS LHS is STRICTLY well-behaved
checkWellBehavedness :: Term -> Bool
checkWellBehavedness term = checkArityConsitency ar && checkWBHelp term w ar
 where w = freeVariablesLHS term
       ar = getArities term

checkWBHelp :: Term -> [Head] -> [(Head,Int)] -> Bool
checkWBHelp term@(Term { nlams = n, sp = children, hd = h}) w ar
    | h `elem` w = all (\child -> (nlams child == 0) && all (\grandchild -> checkWBHelp grandchild w ar) (sp child)) children
    | otherwise = (n > 0 || (sort $ typ term)) && (all (\child -> checkWBHelp child w ar) children)

-- Eta-reduces all the lamdbas which are in FV argument position. Works under the assumption that all
-- SMTRS lhs are EPATs (All lambdas in FV argument positions are eta-reducible)
-- Eta-reduces lambdas in FV argument positions. 
-- Uses a boolean flag to track if we are actively trying to collapse a lambda chain.
etaReduceFVLambdas :: Term -> Term
etaReduceFVLambdas = go False
  where
    -- 1. Free Variables: Look at their immediate arguments.
    -- If an argument is a lambda, we MUST reduce it, so we enter Greedy Mode (True).
    -- If an argument is NOT a lambda, it's safe, so we enter Safe Mode (False).
    go False term@(Term { hd = FV x, sp = children }) = 
        term { sp = checkForLambdas (map checkArg children) }
        
    -- 2. Greedy Mode: We are actively trying to collapse a lambda chain.
    -- Reduce all children recursively.
    go True term@(Term { sp = children }) = 
        term { sp = checkForLambdas (map (go True) children) }
        
    -- 3. Safe Mode: Protects standard function symbols from reduction.
    go False term@(Term { sp = children }) = 
        term { sp = map (go False) children }
        
    -- Helper: Decides the mode based on the FV's immediate argument
    checkArg child@(Term { nlams = n })
        | n > 0     = go True child   -- It's a lambda blocking an FV, crush it!
        | otherwise = go False child  -- It's a function symbol, keep its children safe.

-- Checks if a Term is a lambda expression and if it is tries to eta-reduce it
checkForLambdas :: [Term] -> [Term]
checkForLambdas [] = []
checkForLambdas (term@(Term { nlams = 0, sp = children}):terms) = term : checkForLambdas terms
checkForLambdas (term@(Term { nlams = n, sp = children}):terms)
    | isEtaReducible term = checkForLambdas (shiftDB (-(n-1)) term{ nlams = n - 1, sp = init children } : terms)
    | otherwise = term : checkForLambdas terms


-- Checks if a lambda is eta-reducible
isEtaReducible :: Term -> Bool
isEtaReducible Term{nlams = 0} = False
isEtaReducible Term{hd = DB 0} = False
isEtaReducible (Term {sp = []}) = False
isEtaReducible term@(Term{nlams = n, sp = children})
 | hd (last children) /= DB 0 = False
 | n > 0 = checkDBnFree term{sp = init children} (-n)

-- Checks if the DBn, which we cut off, does not appear anywhere else in the lambda
checkDBnFree :: Term -> Int -> Bool
checkDBnFree (Term{nlams = n, sp = children, hd = DB a}) m = 
    -- 1. Check against (m + n) because DB a is inside this term's lambdas
    a /= (m + n) && all (\child -> checkDBnFree child (m + n)) children

checkDBnFree (Term{nlams = n, sp = children}) m = 
    -- 2. Pass (m + n) to the children. Let them handle their own nlams!
    all (\child -> checkDBnFree child (m + n)) children

-- Shift the DB after cutting one of them off
shiftDB :: Int -> Term -> Term
shiftDB cutoff term@(Term{nlams = n, sp = children, hd = DB m})
    -- 1. Check against (cutoff + n) because DB m is inside this term's lambdas
    | m > (cutoff + n) = term { hd = DB (m - 1), sp = map (\child -> shiftDB (cutoff + n) child) children }
    -- 2. Pass (cutoff + n) to the children. Let them handle their own nlams!
    | otherwise        = term { sp = map (\child -> shiftDB (cutoff + n) child) children }
    
shiftDB cutoff term@(Term{nlams = n, sp = children}) = 
    -- Same here: pass the current scope depth to the children
    term { sp = map (\child -> shiftDB (cutoff + n) child) children }