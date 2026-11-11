module WellBehaved where

import Term.Type
import Term.Ops (freeVars, shiftDB)
import Typ.Ops(sort)
import Typ.Type (Typ(..))
import qualified Data.Set as Set


isEPAT :: Term -> Bool
isEPAT t@(Term { hd = FV _ }) = all argOK (sp t)
  where
    argOK u = Set.null (freeVars u) && nlams (etaReduceRoot u) == 0
isEPAT t = all isEPAT (sp t)


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
    | otherwise = sort (stripLams n (typ term)) && all (\child -> checkWBHelp child w ar) children


-- Eta-reduces all the lamdbas which are in FV argument position. Works under the assumption that all
-- Eta-reduces lambdas in FV argument positions. 
etaReduceFVLambdas :: Term -> Term
etaReduceFVLambdas term@(Term { hd = FV _, sp = children }) = term { sp = map checkArg children } 
 where
 -- Helper: Decides the mode based on the FV's immediate argument
    checkArg child@(Term { nlams = n })
        | n > 0     = etaReduceRoot child
        | otherwise = etaReduceFVLambdas child
etaReduceFVLambdas term@(Term { sp = children }) = term { sp = map etaReduceFVLambdas children }

-- Checks if a Term is a lambda expression and if it is tries to eta-reduce it
checkForLambdas :: [Term] -> [Term]
checkForLambdas [] = []
checkForLambdas (term@(Term { nlams = 0 }):terms) = term : checkForLambdas terms
checkForLambdas (term@(Term { nlams = n, sp = children }):terms)
    | isEtaReducible term = checkForLambdas (shiftDB (-(n-1)) term{ nlams = n - 1, sp = init children } : terms)
    | otherwise = term : checkForLambdas terms


-- Checks if a lambda is eta-reducible
isEtaReducible :: Term -> Bool
isEtaReducible Term{nlams = 0} = False
isEtaReducible Term{hd = DB 0} = False
isEtaReducible (Term {sp = []}) = False
isEtaReducible term@(Term{nlams = n, sp = children})
 | not (isBareDB0 (last children)) = False
 | n > 0 = checkDBnFree term{sp = init children} (-n)


-- Checks if the DBn, which we cut off, does not appear anywhere else in the lambda
checkDBnFree :: Term -> Int -> Bool
checkDBnFree (Term{nlams = n, sp = children, hd = DB a}) m = 
    -- 1. Check against (m + n) because DB a is inside this term's lambdas
    a /= (m + n) && all (\child -> checkDBnFree child (m + n)) children
checkDBnFree (Term{nlams = n, sp = children}) m = 
    -- 2. Pass (m + n) to the children. Let them handle their own nlams!
    all (\child -> checkDBnFree child (m + n)) children

-- | Removes the innermost lambda and the last argument:
--   Precondition: xn occurs nowhere else (checked by isEtaReducible).
dropInnermostLambda :: Term -> Term
dropInnermostLambda t =
  (shiftDB (-1) t { nlams = 0, sp = init (sp t) }) { nlams = nlams t - 1 }

isBareDB0 :: Term -> Bool
isBareDB0 Term{nlams = 0, hd = DB 0, sp = []} = True
isBareDB0 _ = False

stripLams :: Int -> Typ -> Typ
stripLams k (Typ as b) = Typ (drop k as) b

etaReduceRoot :: Term -> Term
etaReduceRoot term@(Term { nlams = n, sp = children })
  | n == 0 || null children = term
  | otherwise =
      let term' = term { sp = init children ++ [etaReduceRoot (last children)] }
      in if isEtaReducible term'
           then etaReduceRoot (dropInnermostLambda term)
           else term