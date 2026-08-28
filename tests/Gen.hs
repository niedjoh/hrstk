{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Gen ( typClosure
           , availMap
           , genTyp
           , genArbitraryTerm
           , genDHP
           , genTermPair
           , genSubst )
where

import Data.List (isSuffixOf,partition)
import Data.List.Extra (splitAtEnd)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tuple.Extra (fst3,snd3,thd3)
import Hedgehog (MonadGen, Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..),Sort)
import Typ.Ops (argTyps,returnSort,arity)
import Term.Type (Term(..),Head(..))
import Term.Ops (isFV,isDBGeq,hdToTerm,addLams,localRestriction)
import Subst.Type (Subst(..))

type AvailMap = Map Sort [(Head,Int,[Typ])]

-- parameters

maxTypArity :: Int
maxTypArity = 5

-- sorts underlying generator

sorts :: [Id]
sorts = [Id "a", Id "b"]

-- type closure

typClosure :: Typ -> [Typ]
typClosure = S.toList . go where
  go b@(Typ as a) = S.unions (S.singleton b : S.singleton (Typ [] a) : map go as)

-- type generation

genSort :: MonadGen m => m Id
genSort = Gen.element sorts

genTyp' :: MonadGen m => m Typ
genTyp' = do
  a <- genSort
  as <- Gen.list (Range.linear 0 maxTypArity) (Gen.small genTyp)
  pure $ Typ as a

genTyp :: MonadGen m => m Typ
genTyp = do
  a <- genSort
  as <- Gen.list (Range.linear 1 maxTypArity) (Gen.small genTyp')
  pure $ Typ as a

-- generate one DB/function symbol/free var per type in input list
-- in practice, a type closure will be provided in order to avoid dead ends
-- in term generation

availMap :: [Typ] -> AvailMap
availMap as = let n = length as in M.fromListWith (++)
  [ ( returnSort a
    , [ (h, length cs, cs)
      | let cs = argTyps a
      , h <- [ DB $ n-i-1
             , F . Id $ "f" <> T.pack (show i)
             , FV . Named . Id $ "Z" <> T.pack (show i)
             ]
      ]
     )
   | (a,i) <- zip as [0..]
   ]

-- term generation

shiftDBs :: Int -> [(Head,Int,[Typ])] -> [(Head,Int,[Typ])]
shiftDBs k = map shiftDB where
  shiftDB (DB i, j, as) = (DB $ i + k, j, as)
  shiftDB p = p

insertNewDBs :: [Typ] -> AvailMap -> AvailMap
insertNewDBs as avail = M.unionsWith (++) (M.map (shiftDBs n) avail : newDBs) where
  n = length as
  newDBs = [ M.singleton (returnSort a) [(DB $ n-i-1, length bs, bs)]
           | (a,i) <- zip as [0..]
           , let bs = argTyps a
           ]

genTermFixedHead :: AvailMap -> Bool -> Int -> Maybe Int -> Typ -> (Head,Int,[Typ]) -> Gen Term
genTermFixedHead availM dhp m onlyDBFrom a (h,_,bs)
  | dhp && isFV h = do
      let availM' = M.map (filter (not . isFV . fst3)) availM
      ts <- Gen.filter localRestriction
                       (traverse (\b -> Gen.small . genTerm availM' True (arity b) (Just 0) $ b) bs1)
      pure $ Term {nlams = n, hd = h, sp = ts, typ = a}
  | otherwise     = do
      j <- Gen.integral (Range.constant 0 (length bs1 - 1))
      ts <- traverse (\(b,i) -> Gen.small . genTerm availM dhp 0 (propagateOnlyDBFrom i j) $ b) (zip bs1 [0..])
      pure $ Term {nlams = n, hd = h, sp = ts ++ dbs, typ = a}
  where
    n = arity a
    (bs1, bs2) = splitAtEnd m bs
    dbs = [hdToTerm b (DB $ m-i-1) | (b,i) <- zip bs2 [0..]]
    propagateOnlyDBFrom i j 
      | Just k <- onlyDBFrom, i == j && (not . isDBGeq k $ h) = onlyDBFrom
      | otherwise                                             = Nothing

genTerm :: AvailMap -> Bool -> Int -> Maybe Int -> Typ -> Gen Term
genTerm availM dhp m onlyDBFrom b@(Typ as a) =
  Gen.recursive Gen.choice (genFun . filterOnlyDBFrom $ nullary) (genFun others) where
    n = length as
    (nullary,others) = partition ((== m) . snd3) . filterAnchorRoot $ availM' M.! a
    availM' = if m > 0 then M.map (shiftDBs n) availM else insertNewDBs as availM
    filterAnchorRoot = if m > 0 then filter ((as `isSuffixOf`) . thd3) else id
    genFun = map (genTermFixedHead availM' dhp m onlyDBFrom' b)
    onlyDBFrom' = (+ n) <$> onlyDBFrom
    filterOnlyDBFrom = case onlyDBFrom' of
      Just i -> filter (isDBGeq i . fst3)
      Nothing -> id
  
genArbitraryTerm :: [Typ] -> AvailMap -> Id -> Gen Term
genArbitraryTerm as availM a = do
  s <- genTerm availM False 0 Nothing (Typ [] a)
  pure $ addLams as s

genDHP :: [Typ] -> AvailMap -> Id -> Gen Term
genDHP as availM a = do
  s <- genTerm availM True 0 Nothing (Typ [] a)
  pure $ addLams as s

genTermPair :: [Typ] -> AvailMap -> ([Typ] -> AvailMap -> Id -> Gen Term) -> ([Typ] -> AvailMap -> Id -> Gen Term) -> Id ->
  Gen (Term,Term)
genTermPair as availM genl genr a = do
  s <- genl as availM a
  t <- genr as availM a
  pure (s,t)

genSubst :: AvailMap -> Map Var Typ -> Gen Subst
genSubst availM m = Subst <$> traverse (genTerm availM False 0 Nothing) m
