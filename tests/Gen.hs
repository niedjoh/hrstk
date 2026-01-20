{-# LANGUAGE OverloadedStrings #-}

module Gen ( GenM
           , runGenM
           , runGenMWith
           , genTyp
           , genTerm
           , genAlmostDHP
           , genDHP
           , genTermPair
           , genDHPPair
           , genDHPAndTerm
           , genSubst )
where

import Control.Monad (replicateM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State (StateT,get,put,runStateT)
import Data.List (isSuffixOf)
import Data.List.Extra (splitAtEnd)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text (pack)
import Data.Tuple.Extra (fst3,snd3,thd3)
import Hedgehog (MonadGen, Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Prettyprinter (Pretty,pretty,vsep)
import Prettyprinter.Render.Text (putDoc)

import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..),Sort)
import Typ.Ops (argTyps,returnSort,arity)
import Term.Type (Term(..),Head(..))
import Term.Ops (isFV,isDHP,hdToTerm)
import Subst.Type (Subst(..))

type AvailMap = Map Sort [(Head,Int,[Typ])]
type GenM = StateT AvailMap (StateT Int Gen)

-- parameters

maxTypArity :: Int
maxTypArity = 3

maxSymbolArity :: Int
maxSymbolArity = 4

-- sorts underlying generator
sorts :: [Id]
sorts = [Id "a", Id "b"]

-- utility functions

tupleTransform :: ((a,b),c) -> (a,b,c)
tupleTransform ((x,y),z) = (x,y,z)

runGenM :: GenM a -> Gen (a, AvailMap, Int)
runGenM x = tupleTransform <$> runStateT (runStateT x M.empty) 0

runGenMWith :: AvailMap -> Int -> GenM a -> Gen (a, AvailMap, Int)
runGenMWith availMap i x = tupleTransform <$> runStateT (runStateT x availMap) i

freshInt :: GenM Int
freshInt = do
  i <- lift $ get
  lift $ put (i+1)
  pure i

-- type generation

genTyp :: MonadGen m => m Typ
genTyp = do
  a <- Gen.element sorts
  as <- Gen.list (Range.linear 0 maxTypArity) (Gen.small genTyp)
  pure $ Typ as a

-- term generation

shiftDBs :: Int -> [(Head,Int,[Typ])] -> [(Head,Int,[Typ])]
shiftDBs k = map shiftDB where
  shiftDB (DB i,j,as) = (DB $ i + k,j,as)
  shiftDB p = p

insertNewDBs :: [Typ] -> AvailMap -> AvailMap
insertNewDBs as avail = M.unionsWith (++) (M.map (shiftDBs n) avail : newDBs) where
  n = length as
  newDBs = [ M.singleton (returnSort a) [(DB $ n-i-1, length bs, bs)]
           | (a,i) <- zip as [0..]
           , let bs = argTyps a
           ]

newFunsAndVars :: Sort -> Int -> GenM [(Head,Int,[Typ])]
newFunsAndVars a k = do
  availFunsVars <- get
  i <- freshInt
  j <- freshInt
  bss <- replicateM 4 $ Gen.list (Range.singleton k) genTyp
  let nas = [ (F . Id $ "f" <> pack (show i), k)
            , (F . Id $ "f" <> pack (show j), k)
            , (FV . Fresh $ i, k)
            , (FV . Fresh $ j, k)
            ]
      news = zipWith (\(x,y) z -> (x,y,z)) nas bss
  put (M.insertWith (++) a news availFunsVars)
  pure news

newDHPArgFun :: Sort -> [Typ] -> Int -> GenM [(Head,Int,[Typ])]
newDHPArgFun a as k = do
  availFunsVars <- get
  i <- freshInt
  bs <- Gen.list (Range.singleton $ k - length as) genTyp
  let new = [(F . Id $ "f" <> pack (show i), k, bs ++ as)]
  put (M.insertWith (++) a new availFunsVars)
  pure new

genTermFixedHead :: AvailMap -> Bool -> Bool -> Typ -> (Head,Int,[Typ]) -> GenM Term
genTermFixedHead availDBs dhp dhpBelowVar a (h,_,bs) = do
  let n = arity a
      gen = if isFV h && dhp then genTerm availDBs True True True else genTerm availDBs dhp False dhpBelowVar
  ts <- traverse (Gen.small . gen) bs
  pure $ Term {nlams = n, hd = h, sp = ts, typ = a}

genDHPVarArgFixedHead :: AvailMap -> Typ -> (Head,Int,[Typ]) -> GenM Term
genDHPVarArgFixedHead availDBs a (h,_,bs) = do
  let n = arity a
      (bs1, bs2) = splitAtEnd n bs
      dbs = [hdToTerm b (DB $ n-i-1) | (b,i) <- zip bs2 [0..]]
  ts <- traverse (Gen.small . genTerm availDBs True False True) bs1
  pure $ Term {nlams = n, hd = h, sp = ts ++ dbs, typ = a}

genTerm :: AvailMap -> Bool -> Bool -> Bool -> Typ -> GenM Term
genTerm availDBs dhp dhpVarArg dhpBelowVar b@(Typ as a) = do
  availFunsVars <- get
  let availDBs' = insertNewDBs as availDBs
      minArity = if dhpVarArg then length as else 0
  k <- Gen.int (Range.linear minArity maxSymbolArity) 
  funsVars <- case M.lookup a availFunsVars of
      Just hds -> do
        case filter ((== k) . snd3) hds of
          [] -> do
            newFunsAndVars a k
          _ -> do
            pure hds
      Nothing -> do
        newFunsAndVars a k
  let dbs = case M.lookup a availDBs' of
        Just hds -> filter ((== k) . snd3) hds
        Nothing -> []        
      genFixedHead = if dhpVarArg then genDHPVarArgFixedHead availDBs else genTermFixedHead availDBs' dhp dhpBelowVar
      heads = if dhpBelowVar || (dhp && M.null availDBs' && k > 0)
        then dbs ++ filter (not . isFV . fst3) funsVars
        else dbs ++ funsVars
  heads' <- if dhpVarArg
    then case filter ((as `isSuffixOf`) . thd3) heads of
      [] -> newDHPArgFun a as k
      filteredHds -> pure filteredHds
    else pure heads
  Gen.choice $ map (genFixedHead b) heads'

genAlmostDHP :: AvailMap -> Typ -> GenM Term
genAlmostDHP avail = genTerm avail True False False

genDHP :: Typ -> GenM Term
genDHP a = Gen.filterT isDHP (genAlmostDHP M.empty a)

genTermPair :: Typ -> GenM (Term,Term)
genTermPair a = do
  s <- genTerm M.empty False False False a
  t <- genTerm M.empty False False False a
  pure (s,t)

genDHPPair :: Typ -> GenM (Term,Term)
genDHPPair a = do
  s <- genDHP a
  t <- genDHP a
  pure (s,t)

genDHPAndTerm :: Typ -> GenM (Term,Term)
genDHPAndTerm a = do
  s <- genDHP a
  t <- genTerm M.empty False False False a
  pure (s,t)

genSubst :: Map Var Typ -> GenM Subst
genSubst m = Subst <$> traverse (genTerm M.empty False False False) m

printSamples :: Pretty a => (Typ -> GenM a) -> Int -> Typ -> IO ()
printSamples gen i a = do
  ps <- replicateM i $ Gen.sample $ runGenM $ gen a
  putDoc (vsep . map (pretty . fst3) $ ps)
  putStrLn ""

printTermSamples :: Int -> Typ -> IO ()
printTermSamples = printSamples (Gen.resize 50 . genTerm M.empty False False False)

printDHPSamples :: Int -> Typ -> IO ()
printDHPSamples = printSamples (Gen.resize 50 . genDHP)

printAlmostDHPSamples :: Int -> Typ -> IO ()
printAlmostDHPSamples = printSamples (Gen.resize 50 . genAlmostDHP M.empty)
