-- |implementation of NCPO
module Termination.NCPO.Ordering where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (ReaderT,runReaderT,asks)
import Data.List ((\\))
import Data.Set (Set)
import qualified Data.Set as S
import Language.Hasmtlib (Equatable(..),Orderable(..),Boolean(..),and,or,false)

import Utils.Type (Accessor(..),Var,Id)
import Utils.SMT (Constraint,(<&&>),(<&&),(<||>))
import Utils.FreshMonad (FreshM,freshVar)
import Typ.Type (Typ(..))
import Typ.Ops (equatableByTypApp,posOf)
import Term.Type (Term(..),Head(..))
import Term.Ops (hdToTerm,danglingDB)
import Subst.Ops (applyAbsToVar,applyAbsToTerms)
import Termination.NCPO.Type (CPOInfo(..),IsStatus(..))

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
    allPossibilities [] = [[]]
    allPossibilities (xs:xss) = concat [map (x:) (allPossibilities xss) | x <- xs]
sso varRec _ s t = ncpo varRec Compare S.empty s t
