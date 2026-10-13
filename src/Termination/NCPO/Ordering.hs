-- |implementation of NCPO
module Termination.NCPO.Ordering where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (ReaderT,runReaderT,asks, withReaderT)
import Data.List ((\\))
import Data.Set (Set)
import qualified Data.Set as S
import Language.Hasmtlib (Equatable(..),Orderable(..),Boolean(..),and,or,false, ite, (==>))

import Utils.Type (Accessor(..),Var,Id)
import Utils.Misc (allPossibilities)
import Utils.SMT (Constraint,(<&&>),(<&&),(<||>))
import Utils.FreshMonad (FreshM,freshVar)
import Typ.Type (Typ(..))
import Typ.Ops (equatableByTypApp,posOf)
import Term.Type (Term(..),Head(..))
import Term.Ops (hdToTerm,danglingDB)
import Subst.Ops (applyAbsToVar,applyAbsToTerms)
import Termination.NCPO.Type (CPOInfo(..),IsStatus(..),CPOInfoFilter(..))
import Control.Monad (forM, forM_)
import Debug.Trace (traceM)

-- |custom data type which indicates whether types should be compared in a given NCPO call
data TypeComparison = Compare | NoCompare

type CompareFun a b = Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
type ApplCompareFun a b = Term -> ReaderT (CPOInfo a b) FreshM Constraint

-- |if-like function for 'TypeComparison'
ifCompare :: TypeComparison -> a -> a -> a
ifCompare Compare x _ = x
ifCompare NoCompare _ y = y

-- |A wrapper for NCPO
ncpoWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term ->
  FreshM Constraint
ncpoWrapper cpoinfo s t = runReaderT (ncpo False Compare S.empty s t) cpoinfo

ncpoWeakWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term ->
  FreshM Constraint
ncpoWeakWrapper cpoinfo s t = runReaderT (ncpoWeak False Compare S.empty s t) cpoinfo

-- |Implementation of NCPO
ncpo :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> TypeComparison -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
ncpo varRec typeComp vars s@(Term {typ = Typ [] _}) t = do
  ifCompare typeComp (weakTypeOrder (typ s) (typ t)) (pure true) <&&> case hd s of
    F f -> if any (== t) (S.map (\(v,c) -> hdToTerm c (FV v)) vars)
      then pure true
      else or <$> traverse (\u -> bawo varRec u t) (sp s) <||> case typ t of
        Typ (b:_) _ -> do
          z <- lift freshVar
          ncpo varRec NoCompare (S.insert (z,b) vars) s (applyAbsToVar t z)
        Typ [] c -> case hd t of
          F g -> funFunCase varRec vars s f g (sp s) (sp t)
          FV var -> if varRec
            then pure false
            else ncpo True NoCompare vars s (hdToTerm (Typ (map typ $ sp t) c) (FV var)) <&&>
                 (and <$> traverse (ncpo False NoCompare vars s) (sp t))
          _ -> error "impossible case"
    _ -> pure false
ncpo varRec typeComp vars s@(Term {typ = Typ (a:_) _}) t =
  ifCompare typeComp (weakTypeOrder (typ s) (typ t)) (pure true) <&&> do
     z <- lift freshVar
     let s' = applyAbsToVar s z
         t' = applyAbsToVar t z
     ncpoWeak varRec Compare vars s' t <||> case typ t of
       Typ (b:_) _ -> if a == b
         then ncpo varRec NoCompare vars s' t'
         else ncpo varRec NoCompare vars s t'
       _ -> ncpo varRec NoCompare vars s' t

-- |case s = f(ss) > g(ts) where f is big
funFunCase :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Set (Var,Typ) -> Term -> Id -> Id -> [Term] -> [Term] ->
  ReaderT (CPOInfo a b) FreshM Constraint
funFunCase varRec vars s f g ss ts = do
  st <- asks stat
  funPrec <- asks fPrec
  let mulLex = (isLex (st ! f) <&& ncpoLex (sso varRec vars) (ncpo varRec NoCompare vars s) ss ts) <||>
               (isMul (st ! f) <&& ncpoMul (sso varRec vars) ss ts)
  if f == g
    then mulLex
    else funPrec ! f >? funPrec ! g <&& (and <$> traverse (ncpo varRec NoCompare vars s) ts) <||>
         (funPrec ! f === funPrec ! g && st ! f === st ! g) <&& mulLex

-- |lexicographic extension of NCPO generalized by comparison functions
ncpoLex :: (Orderable a, IsStatus b, Equatable b) =>
  CompareFun a b -> ApplCompareFun a b -> [Term] -> [Term] ->
  ReaderT (CPOInfo a b) FreshM Constraint
ncpoLex comp applComp = go where
  go [] _ = pure false
  go _ [] = pure false
  go (si:ssr) (ti:ttr) = if si == ti
    then go ssr ttr
    else comp si ti <&&> (and <$> traverse applComp ttr)

-- |multiset extension of NCPO generalized by comparison function
ncpoMul :: (Orderable a, IsStatus b, Equatable b) =>
  CompareFun a b -> [Term] -> [Term] -> ReaderT (CPOInfo a b) FreshM Constraint
ncpoMul _ [] [] = pure false
ncpoMul comp ss ts = if null x
  then pure false
  else and <$> traverse (\t -> or <$> traverse (\s -> comp s t) y) x where
    x = ts \\ ss
    y = ss \\ ts

-- |weak NCPO orientation (reflexive closure)
ncpoWeak :: (Orderable a, IsStatus b, Equatable b) =>
 Bool -> TypeComparison  -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
ncpoWeak varRec typComp vars s t = if s == t
  then pure true
  else ncpo varRec typComp vars s t

-- |A strict order on types for NCPO as defined in the 2015 LMCS article
typeOrder :: Orderable a => Typ -> Typ -> ReaderT (CPOInfo a b) FreshM Constraint
typeOrder (Typ [] a) (Typ [] b) = do
  sortPrec <- asks sPrec
  pure $ sortPrec ! a >? sortPrec ! b
typeOrder (Typ (a:as) b) c = if Typ as b == c
  then pure true
  else case c of
    Typ (d:ds) e -> if a == d
      then typeOrder (Typ as b) (Typ ds e)
      else pure false
    _ -> pure false
typeOrder _ _ = pure false

-- |reflexive closure of 'typeOrder'
weakTypeOrder :: Orderable a => Typ -> Typ -> ReaderT (CPOInfo a b) FreshM Constraint
weakTypeOrder a b = if a == b
  then pure true
  else typeOrder a b

-- |The two arguments are connected by the composition of the following relations:
-- * reflexive closure of basic subterm relation
-- * reflexive closure of accessibility relation
-- * weak orient with NCPO
--
-- Note that we only allow to proceed to subterms via "nonversatile paths"
bawo :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
bawo varRec s t = awo varRec s t <||> go s t where
  varCond u = not . bool $ danglingDB u
  go u@(Term {hd = F _, typ = Typ _ a}) v = do
      basic <- asks isBasic
      let u' = u{nlams = 0, typ = Typ [] a}
      ((basic ! a && varCond v) <&& awo varRec u' v) <||> (or <$> traverse (\w -> go w v) (sp u))
  go _ _ = pure false

-- |accessibility subterm relation with generic compare function for base case
accSubt :: CompareFun a b -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
accSubt comp s@(Term {hd = F f}) t = do
  acc <- asks isAccessible
  or <$> traverse (\(u,i) -> acc ! (f,i) <&& (comp u t <||> accSubt comp u t))  (zip (sp s) [0..])
accSubt _ _ _ = pure false

-- |The two arguments are connected by the composition of the following relations:
-- * reflexive closure of accessibility relation
-- * weak orient with NCPO
--
-- Note that we only allow to proceed to subterms for applied function symbols
awo :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
awo varRec s t =
  ncpoWeak varRec Compare S.empty s t <||> accSubt (ncpoWeak varRec Compare S.empty) s t

-- |structurally smaller + orient with variable set reset
sso :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
sso varRec vars s@(Term {typ = Typ [] a}) t =
  ncpo varRec Compare S.empty s t <||> accSubt comp s t where
    comp u _ = case equatableByTypApp (typ s) (typ u) of
        Nothing -> pure false
        Just cs -> do
          let candidateVars = [filter ((== c) . snd) (S.toList vars) | c <- cs]
          if [] `elem` candidateVars || any (\c -> bool $ posOf a c /= S.empty) cs
            then pure false
            else do
              let possibleVarLists = allPossibilities candidateVars
                  toTerm (x,c) = hdToTerm c (FV x)
                  f xs = case applyAbsToTerms u (map toTerm xs) of
                    Just uxs -> pure . bool $ uxs == t
                    Nothing -> pure false
              or <$> traverse f possibleVarLists
sso varRec _ s t = ncpo varRec Compare S.empty s t


{-
#################################################################################################################
#################################################################################################################
#################################################################################################################
#################################################################################################################
#################################################################################################################
-}

type CompareFunFilter a b = Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
type ApplCompareFunFilter a b = Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint

ncpoWrapperFilter :: (Orderable a, IsStatus b, Equatable b) => CPOInfoFilter a b -> Term -> Term ->
  FreshM Constraint
ncpoWrapperFilter cpoinfoFilter s t = runReaderT (ncpoFilter False Compare S.empty s t) cpoinfoFilter

ncpoWeakWrapperFilter :: (Orderable a, IsStatus b, Equatable b) => CPOInfoFilter a b -> Term -> Term ->
  FreshM Constraint
ncpoWeakWrapperFilter cpoinfoFilter s t = runReaderT (ncpoWeakFilter False Compare S.empty s t) cpoinfoFilter



ncpoFilter :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> TypeComparison -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
ncpoFilter varRec typeComp vars s@(Term {typ = Typ [] _}) t = do
  setMap <- asks filterSet
  inMap <- asks filterIn
  ifCompare typeComp (withReaderT base (weakTypeOrder (typ s) (typ t))) (pure true) <&&> case hd s of
    F f -> do
      collapseLeft <- do
        disjs <- forM (zip [1..] (sp s)) $ \(i, si) ->
          (inMap ! (f,i) &&) <$> ncpoFilter varRec typeComp vars si t
        return (not (setMap ! f) && or disjs)
      headedCase <- (setMap ! f &&) <$> (
        if any (== t) (S.map (\(v,c) -> hdToTerm c (FV v)) vars)
          then pure true
          else (or <$> forM (zip [1..] (sp s)) (\(i, u) -> (inMap ! (f,i) &&) <$> bawoFilter varRec u t)) <||> case typ t of
            Typ (b:_) _ -> do
              z <- lift freshVar
              ncpoFilter varRec NoCompare (S.insert (z,b) vars) s (applyAbsToVar t z)
            Typ [] c -> case hd t of
              F g -> do
                collapseRight <- do
                  disjs <- forM (zip [1..] (sp t)) $ \(j, tj) ->
                    (inMap ! (g,j) &&) <$> ncpoFilter varRec typeComp vars s tj
                  return (not (setMap ! g) && or disjs)
                noCollapse <- funFunCaseFilter varRec vars s t f g (sp s) (sp t)
                return (collapseRight || noCollapse)
              FV var -> if varRec
                then pure false
                else ncpoFilter True NoCompare vars s (hdToTerm (Typ (map typ $ sp t) c) (FV var)) <&&>
                    (and <$> traverse (ncpoFilter False NoCompare vars s) (sp t))
              _ -> error "impossible case")
      return (collapseLeft || headedCase)
    _ -> pure false
ncpoFilter varRec typeComp vars s@(Term {typ = Typ (a:_) _}) t =
  ifCompare typeComp (withReaderT base (weakTypeOrder (typ s) (typ t))) (pure true) <&&> do
     z <- lift freshVar
     let s' = applyAbsToVar s z
         t' = applyAbsToVar t z
     ncpoWeakFilter varRec Compare vars s' t <||> case typ t of
       Typ (b:_) _ -> if a == b
         then ncpoFilter varRec NoCompare vars s' t'
         else ncpoFilter varRec NoCompare vars s t'
       _ -> ncpoFilter varRec NoCompare vars s' t


bawoFilter :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
bawoFilter varRec s t = awoFilter varRec s t <||> go s t
 where
  varCond u = not . bool $ danglingDB u
  go u@(Term {hd = F g, typ = Typ _ a}) v = do
    basic <- asks (isBasic . base)
    inMap <- asks filterIn
    let u' = u{nlams = 0, typ = Typ [] a}
    here   <- (basic ! a && varCond v) <&& awoFilter varRec u' v
    deeper <- forM (zip [1..] (sp u)) $ \(i, w) -> do
      c <- go w v
      pure (inMap ! (g,i) && c)
    pure (here || or deeper)
  go _ _ = pure false


awoFilter :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
awoFilter varRec s t =
  ncpoWeakFilter varRec Compare S.empty s t <||> accSubtFilter False (ncpoWeakFilter varRec Compare S.empty) s t


equalFilter :: (Orderable a, IsStatus b, Equatable b) =>
 Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
equalFilter s t
 | nlams s /= nlams t || typ s /= typ t = pure false
 | otherwise = do
    setMap <- asks filterSet
    inMap <- asks filterIn
    let n = length $ sp s
    let m = length $ sp t

    case (hd s, hd t) of

      (F f, F g) | f == g -> do
        let m = length (sp t)
        if n /= m then return false else do
          const <- forM [1 .. n] $ \i -> do
            recursive <- equalFilter (sp s !! (i-1)) (sp t !! (i-1))
            return (inMap ! (f,i) ==> recursive)
          return (and const)

      (F f, F g) -> do
        let setS = setMap ! f
        let setT = setMap ! g
        fCollapse <- do 
          const <- forM [1 .. n] $ \i -> do
            recursive <- equalFilter (sp s !! (i-1)) t
            return (inMap ! (f,i) && recursive)
          return (not setS && or const)

        gCollapse <- do 
          const <- forM [1 .. m] $ \i -> do
            recursive <- equalFilter s (sp t !! (i-1))
            return (inMap ! (g,i) && recursive)
          return (not setT && or const)

        return (fCollapse || gCollapse)

      (F f, _) -> do
        let setS = setMap ! f
        const <- forM [1 .. n] $ \i -> do
          recursive <- equalFilter (sp s !! (i-1)) t
          return (inMap ! (f,i) && recursive)
        return (not setS && or const)

      (_, F g) -> do
        let setT = setMap ! g
        const <- forM [1 .. m] $ \i -> do
          recursive <- equalFilter s (sp t !! (i-1))
          return (inMap ! (g,i) && recursive)
        return (not setT && or const)

      (hs, ht)
        | hs == ht -> do
            if n /= m
              then pure false
              else do
                eqs <- forM [1 .. n] $ \i ->
                  equalFilter (sp s !! (i-1)) (sp t !! (i-1))
                pure (and eqs)
        | otherwise -> pure false

ncpoWeakFilter :: (Orderable a, IsStatus b, Equatable b) =>
 Bool -> TypeComparison  -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
ncpoWeakFilter varRec typComp vars s t = do
  equality <- equalFilter s t
  strict <- ncpoFilter varRec typComp vars s t
  return (equality || strict)


accSubtFilter :: Bool -> CompareFunFilter a b -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
accSubtFilter strictStep comp s@(Term {hd = F f}) t = do
  acc   <- asks (isAccessible . base)
  setMap <- asks filterSet
  inMap <- asks filterIn
  let setGate = if strictStep then setMap ! f else true
  results <- forM (zip (sp s) [0..]) $ \(u,i) -> do
    c1 <- comp u t
    c2 <- accSubtFilter strictStep comp u t
    pure ((setGate && acc ! (f,i) && inMap ! (f,i+1)) && (c1 || c2))
  pure (or results)
accSubtFilter _ _ _ _ = pure false


ssoFilter :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfoFilter a b) FreshM Constraint
ssoFilter varRec vars s@(Term {typ = Typ [] a}) t =
  ncpoFilter varRec Compare S.empty s t <||> accSubtFilter True comp s t where
    comp u _ = case equatableByTypApp (typ s) (typ u) of
        Nothing -> pure false
        Just cs -> do
          let candidateVars = [filter ((== c) . snd) (S.toList vars) | c <- cs]
          if [] `elem` candidateVars || any (\c -> bool $ posOf a c /= S.empty) cs
            then pure false
            else do
              let possibleVarLists = allPossibilities candidateVars
                  toTerm (x,c) = hdToTerm c (FV x)
                  f xs = case applyAbsToTerms u (map toTerm xs) of
                    Just uxs -> pure . bool $ uxs == t
                    Nothing -> pure false
              or <$> traverse f possibleVarLists
ssoFilter varRec _ s t = ncpoFilter varRec Compare S.empty s t


funFunCaseFilter :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Set (Var,Typ) -> Term -> Term -> Id -> Id -> [Term] -> [Term] ->
  ReaderT (CPOInfoFilter a b) FreshM Constraint
funFunCaseFilter varRec vars s t f g ss ts = do
  traceM ("funFunCase: " ++ show s ++ " vs " ++ show t)
  st <- asks (stat . base)
  funPrec <- asks (fPrec . base)
  setMap <- asks filterSet
  inMap <- asks filterIn
  let mulLex = (isLex (st ! f) <&& ncpoLexFilter (ssoFilter varRec vars) (ncpoFilter varRec NoCompare vars s) t f ss ts) 
     -- <||> (isMul (st ! f) <&& ncpoMul (ssoFilter varRec vars) ss ts) dropped for now
  if f == g
    then mulLex
    else do
      let precedence = funPrec ! f >? funPrec ! g
      conjs <- do
        cs <- forM [1 .. (length ts)] $ \j -> do
          strict <- ncpoFilter varRec NoCompare vars s (ts !! (j-1))
          return (inMap ! (g,j) ==> strict)
        return (and cs)
      disjs <- do
        ds <- forM [1 .. (length ss)] $ \i -> do
          eq <- equalFilter (ss !! (i-1)) t
          strict <- ncpoFilter varRec NoCompare vars (ss !! (i-1)) t
          return (inMap ! (f,i) && (eq || strict))
        return (or ds)
      eqPrecCase <- if length ss == length ts
        then do
          ml <- mulLex
          let aligned = and [ (inMap ! (f,i) ==> inMap ! (g,i)) && (inMap ! (g,i) ==> inMap ! (f,i))
                            | i <- [1 .. length ss] ]
          pure ((funPrec ! f === funPrec ! g) && (st ! f === st ! g)
                && setMap ! f && setMap ! g && aligned && ml)
        else pure false
      return (((setMap ! f) && (setMap ! g) && ((precedence && conjs) || disjs)) || eqPrecCase)
         


-- |lexicographic extension of NCPO generalized by comparison functions
ncpoLexFilter :: (Orderable a, IsStatus b, Equatable b) =>
  CompareFunFilter a b -> ApplCompareFunFilter a b -> Term -> Id -> [Term] -> [Term] ->
  ReaderT (CPOInfoFilter a b) FreshM Constraint
ncpoLexFilter comp applComp t f ss tt = do
  setMap <- asks filterSet
  inMap <- asks filterIn
  disjA <- do
    disjs <- forM (zip ss [1..]) $ \(si, i) -> do
      eq      <- equalFilter si t
      greater <- comp si t
      return (inMap ! (f,i) && (eq || greater))
    return (or disjs)
  disjB <- do
    disjs <- forM (zip ss [1..]) $ \(si, i) -> do
      let inConst = inMap ! (f,i)
      strict <- comp si (tt !! (i-1))
      before <- do
        conjs <- forM [1 .. (i-1)] $ \j -> do
          eq <- equalFilter (ss !! (j-1)) (tt !! (j-1))
          return ((inMap ! (f,j)) ==> eq)
        return (and conjs)
      after <- do
        conjs <- forM [(i+1) .. (length ss)] $ \j -> do
          greater <- applComp (tt !! (j-1))
          return ((inMap ! (f,j)) ==> greater)
        return (and conjs)
      return (inConst && strict && before && after)
    return (or disjs)
  return (setMap ! f && (disjA || disjB))






