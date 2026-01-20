{-# LANGUAGE OverloadedStrings #-}

-- |implementation of unification of DHPs
module Subst.Unif where

import Control.Monad (guard)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import qualified Data.Set as S
import Control.Monad (replicateM)
import Prettyprinter (Doc,line,vsep,pretty)

import Utils.Type (Var(..),Id(..))
import Utils.FreshMonad (MonadFresh,FreshM, freshVar)
import Typ.Type (Typ(..),Sort)
import Typ.Ops (arity,argTyps)
import Term.Type (Term(..),Head(..))
import Term.Ops (freeVars,hdToTerm,addLams)
import Subst.Type (Subst(..))
import Subst.Ops (empty,singleton,restrictToVars,compose,applyToPair,discharge)
import Subst.Match (match)
import Equation.Type (Equation)

data UnifCase = Fail
              | Rem 
              | Dec Term Term
              | Var Var Term
              | Prj Var Typ Int [Term]
              | ImtPrj Bool (Term,Term) Var Typ [Typ] Id [Term]
              | FFE Var Sort [Term] [Term]
              | FFN Var Var Int Sort [Term] [Term]

-- |Computes a minimal complete set of unifiers of the two terms.
unif :: Term -> Term -> MaybeT FreshM [Subst]
unif lterm rterm =
  map (restrictToVars vars) <$> go [(lterm,rterm)] M.empty empty where
    vars = freeVars lterm `S.union` freeVars rterm
    findVar var = M.findWithDefault [] var
    deleteVar var = M.delete var
    go (tp:tps) pm subst = case unifCase tp of
      Fail -> return []
      Rem -> go tps pm subst
      Dec s t -> go (tps ++ zip (map absSubt (sp s)) (map absSubt (sp t))) pm subst where
        absSubt = addLams (argTyps . typ $ s)
      Var var t -> go (applySubst $ tps ++ findVar var pm)
                      (deleteVar var pm)
                      (compose varToT subst) where
        varToT = singleton var t
        applySubst = map (applyToPair varToT)
      Prj var a i ss -> do
        varToUs <- prj var a i ss
        concat <$> sequence [ go (map (applyToPair varToU) $ (tp:tps) ++ findVar var pm)
                                 (deleteVar var pm)
                                 (compose varToU subst)
                            | varToU <- varToUs
                            ]
      ImtPrj True tp' var a as f ss -> do -- fail or postpone if variable also occurs on right-hand side
        varToUs <- imtPrj var a as f ss
        case varToUs of
          [] -> error "impossible case"
          (_:projections) -> if any isJust [uncurry (flip match) . applyToPair p $ tp' | p <- projections]
            then go tps (M.insertWith (++) var [tp] pm) subst 
            else return []
      ImtPrj False _ var a as f ss -> do
        varToUs <- imtPrj var a as f ss
        concat <$> sequence [ go (map (applyToPair varToU) $ (tp:tps) ++ findVar var pm)
                                 (deleteVar var pm)
                                 (compose varToU subst)
                            | varToU <- varToUs
                            ]
      FFE var a ss ts -> do
        varToU <- ffe var a ss ts
        go (map (applyToPair varToU) $ tps ++ findVar var pm)
           (deleteVar var pm)
           (compose varToU subst)
      FFN sVar tVar k a ss ts -> do
        stVarsToUV <- ffn sVar tVar k a ss ts
        go (map (applyToPair stVarsToUV) $ tps ++ findVar sVar pm ++ findVar tVar pm)
           (deleteVar sVar $ deleteVar tVar pm)
           (compose stVarsToUV subst)
    go [] pm subst = do
      guard $ M.null pm
      return [subst]

-- |Determines the best applicable inference rule(s) for a given term pair.
unifCase :: (Term,Term) -> UnifCase
unifCase (s,t)
  | typ s /= typ t = Fail
  | s == t         = Rem
  | FV _ <- hd t   = cases t s -- handle symmetric cases
  | otherwise      = cases s t
  where
    cases u@(Term {hd = FV uVar, typ = Typ _ b}) v@(Term {hd = FV vVar})
      | uVar == vVar = FFE uVar b (sp u) (sp v)
      | varCond u uVar v = Var uVar v
      | otherwise   = FFN uVar vVar (nlams u) b (sp u) (sp v)
    cases u@(Term {hd = FV var, typ = Typ _ b}) v
      | varCond u var v = Var var v
      | F f <- hd v = ImtPrj (var `S.member` freeVars v) (u,v) var a (map typ (sp v)) f (sp u)
      | DB i <- hd v = if var `S.member` freeVars v then Fail else Prj var a i (sp u)
      where
        bs = map typ (sp u)
        a = Typ bs b
    cases u v
      | hd u == hd v = Dec u v
      | otherwise = Fail
    varCond u var v = sp u == [ hdToTerm a (DB $ nlams u - i - 1)
                              | (a,i) <- zip (argTyps $ typ u) [0..] ]
                      && var `S.notMember` (freeVars v)

prj :: MonadFresh m => Var -> Typ -> Int -> [Term] -> m [Subst]
prj var a i ss = do
  let n = length ss
  let args = [(DB (n-j-1), argTyps . typ $ sj) | (sj,j) <- zip ss [0..], hd sj == DB (i + nlams sj)]
  pbs <- sequence [partialBinding a dbj bs | (dbj,bs) <- args]
  return $ map (singleton var) pbs

imtPrj :: MonadFresh m => Var -> Typ -> [Typ] -> Id -> [Term] -> m [Subst]
imtPrj var a as f ss = do
  let n = length ss
  let args = [(DB (n-j-1), argTyps . typ $ sj) | (sj,j) <- zip ss [0..], hd sj == F f]
  ib <- partialBinding a (F f) as
  pbs <- sequence [partialBinding a dbj bs | (dbj,bs) <- args]
  return $ map (singleton var) (ib : pbs)

ffe :: MonadFresh m => Var -> Sort -> [Term] -> [Term] -> m Subst
ffe var a ss ts = do
  x <- freshVar
  let n = length ss
      dbs = [hdToTerm (typ si) (DB (n-i-1)) | (si,ti,i) <- zip3 ss ts [0..], si == ti]
      u = Term {nlams = n, hd = FV x, sp = dbs, typ = Typ (map typ ss) a}
  return $ singleton var u

ffn :: MonadFresh m => Var -> Var -> Int -> Sort -> [Term] -> [Term] -> m Subst
ffn sVar tVar k a ss ts = do
  x <- freshVar
  let n = length ss
      m = length ts
      p1 = [ (hdToTerm (typ si) (DB (n-i-1)), w)
           | (si,i) <- zip ss [0..]
           , Just w <- [discharge k [(tj,m-j-1) | (tj,j) <- zip ts [0..]] si]
           , S.null (freeVars w)
           ]
      p2 = [ (w, hdToTerm (typ ti) (DB (m-i-1)))
           | (ti,i) <- zip ts [0..]
           , Just w <- [discharge k [(sj,n-j-1) | (sj,j) <- zip ss [0..]] ti]
           , S.null (freeVars w)
           ]
      (us,vs) =  unzip . nub $ p1 ++ p2
      u = Term {nlams = n, hd = FV x, sp = us, typ = Typ (map typ ss) a}
      v = Term {nlams = m, hd = FV x, sp = vs, typ = Typ (map typ ts) a}
  return $ compose (singleton sVar u) (singleton tVar v)

-- |Generates a partial binding with the given type and head symbol.
partialBinding :: MonadFresh m => Typ -> Head -> [Typ] -> m Term
partialBinding a@(Typ as _) h bs = do
  xs <- replicateM (length bs) freshVar
  let n = arity a
      args = [ Term {nlams = k
                   , hd = FV x
                   , sp = [hdToTerm c (DB (n+k-i-1))  | (c,i) <- zip (as ++ cs) [0..]]
                   , typ = d
                   }
             | (x,d@(Typ cs _)) <- zip xs bs, let k = arity d
             ]
  return $ Term {nlams = n, hd = h, sp = args, typ = a}

resultDoc :: Equation -> [Subst] -> Doc ann
resultDoc e substs = line <> "input DHP unification problem: " <> line <> line <>
  pretty e <> line <> line <> "unifiers:" <> line <>
  if null substs
    then "none" <> line <> line
    else line <> vsep (map pretty substs) <> line <> line
