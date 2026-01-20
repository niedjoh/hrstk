{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Utils.TypeInference where

import Data.Either.Extra (mapRight)
import Data.List ((!?))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Tuple.Extra (second,third3)
import Data.Void (Void)
import Prettyprinter (Doc,(<+>),pretty,vsep)
import Text.Megaparsec (ParseError)

import Utils.ITerm (IHead(..),ITerm(..),IEquation(..),Pos,ipos,mityp)
import Utils.Parse (constructErrorGeneric)
import Typ.Type (Typ(..),Sort)

data ETyp = ETyp [ETyp] (Either (IHead,Int,Int) Sort) deriving Show
type Constr = (IHead,Pos,ETyp)

-- |Converts a Typ to an ETyp.
typToETyp :: Typ -> ETyp
typToETyp (Typ as a) = ETyp (map typToETyp as) (Right a)

-- |Converts an ETyp to a Typ if possible.
typFromETyp :: ETyp -> Maybe Typ
typFromETyp (ETyp _ (Left _)) = Nothing
typFromETyp (ETyp etyps (Right a)) = do
  as <- mapM typFromETyp etyps
  return $ Typ as a

-- |Version of liftTyp for ETyp.
liftETyp :: [ETyp] -> ETyp -> ETyp
liftETyp eas (ETyp ebs eb) = ETyp (eas ++ ebs) eb

-- |Construct a type check error.
constructTCError :: ITerm -> Doc ann -> Doc ann -> ParseError Text Void
constructTCError t d1 d2 = constructErrorGeneric (ipos t) doc where
  doc = vsep [ "type check failed"
             , "have" <+> pretty t <> ":" <+> d1
             , "want" <+> pretty t <> ":" <+> d2
             ]

constructTooManyArgsError :: Int -> IHead -> ParseError Text Void
constructTooManyArgsError i ih = constructErrorGeneric i doc where
  doc = vsep [ "type check failed"
             , pretty ih <+> "is applied to too many arguments"
             ]

-- |Construct a type inference error.
constructTIError :: Int -> Doc ann -> ParseError Text Void
constructTIError i d = constructErrorGeneric i doc where
  doc = vsep ["type inference failed",d]

-- |Construct a type inference/check error.
constructTICError :: Int -> IHead -> Doc ann -> Doc ann -> ParseError Text Void
constructTICError i ih d1 d2 = constructErrorGeneric i doc where
  doc = vsep [ "type inference failed"
             , "inferred at another position" <+> pretty ih <> ":" <+> d1
             , "want" <+> pretty ih <> ":" <+> d2
             ]

-- |Type inference.
inferTypeITerm :: Typ -> ITerm -> Either (ParseError Text Void) [Constr]
inferTypeITerm typ = mapRight snd . go (Right typ) where
  go ec s@(IMat p ih (Just (Typ as a)) ts)
    | k > length as = Left $ constructTooManyArgsError p ih
    | Right c <- ec, c /= c' = Left $ constructTCError s (pretty c') (pretty c)
    | otherwise = (typToETyp c',) . concat . map snd <$> traverse (uncurry go) (zip (map Right as) ts)
    where
      k = length ts
      c' = Typ (drop k as) a
  go ec (IMat p ih Nothing ts) = do
    (ebs,constrs) <- second concat . unzip <$> traverse (\(t,i) -> go (Left (ih,i,0)) t) (zip ts [0..])
    let etyp = case ec of
          Right c -> typToETyp c
          Left (_,_,_) -> ETyp [] $ Left (ih,-1,length ts)
        ecAsETyp = case ec of
          Right c -> typToETyp c
          Left (ih',i,j) -> ETyp [] $ Left (ih',i,j)
    Right (etyp, (ih,p,liftETyp ebs ecAsETyp) : constrs)
  go (Right c@(Typ [] _)) s@(ILam _ _ a _) = Left $ constructTCError s (pretty a <+> "> *") (pretty c)
  go (Right c@(Typ (b:bs) d)) s@(ILam _ _ a t)
    | a /= b = Left $ constructTCError s (pretty a <+> "> *") (pretty c)
    | otherwise = do
        (ec,constrs) <- go (Right $ Typ bs d) t
        Right (liftETyp [typToETyp a] ec, constrs)
  go (Left (ih,i,j))  (ILam _ _ a t) = do
    (ec,constrs) <- go (Left (ih,i,j+1)) t
    Right (liftETyp [typToETyp a] ec, constrs)

-- |Solve generated type constraints.
solveConstraints :: [Constr] -> Either (ParseError Text Void) (Map IHead Typ)
solveConstraints = go False M.empty [] where
  go _ m [] [] = Right m
  go True m ps@(_:_) [] = go False m [] ps
  go False _ ((hd,p,_):_) [] = Left $ constructTIError p $ "information about" <+> pretty hd <+> "not sufficient"
  go changed m ps (c@(hd,p,ea):cs)
    | Just a <- typFromETyp ea = case m M.!? hd of
        Just b -> if a == b
          then go changed m ps cs
          else Left $ constructTICError p hd (pretty b) (pretty a)
        Nothing -> let
          m' = M.insert hd a m
          f = third3 (apply m')
          in go True m' (map f ps) (map f cs)
    | otherwise = go changed m (c:ps) cs
  apply m (ETyp ets r@(Right _)) = ETyp (map (apply m) ets) r
  apply m (ETyp ets l@(Left (hd,i,j))) = case m M.!? hd of
    Just a -> case extractTyp a i of
      Just (Typ bs b) -> if length bs >= j
        then ETyp (map (apply m) ets ++ map typToETyp (drop j bs)) (Right b)
        else error "impossible case"
      Nothing -> error "impossible case"
    Nothing -> ETyp (map (apply m) ets) l
  extractTyp a (-1) = Just a
  extractTyp (Typ as a) i = (as ++ [Typ [] a]) !? i

-- |Enrich the type information of an equation by the inferred types
addInferredTypes :: Map IHead Typ -> IEquation -> IEquation
addInferredTypes m ieq = ieq{ilhs = go $ ilhs ieq, irhs = go $ irhs ieq} where
  go (IMat p ih Nothing ts) = case m M.!? ih of
    Just a -> IMat p ih (Just a) (map go ts)
    _ -> error "type inference missing"
  go (IMat p ih ja ts) = IMat p ih ja (map go ts)
  go (ILam p idt a t) = ILam p idt a (go t)

-- |Checks whether both sides of an equation are well-typed and have the same type
inferTypeIEq :: IEquation -> Either (ParseError Text Void) (IEquation,Typ)
inferTypeIEq ie = do
  let p = ipos $ ilhs ie
  case catMaybes [mityp $ ilhs ie, mityp $ irhs ie] of
    a:_ -> do
      constr1 <- inferTypeITerm a (ilhs ie)
      constr2 <- inferTypeITerm a (irhs ie)
      m <- solveConstraints (constr1 ++ constr2)
      return $ (addInferredTypes m ie, a)
    [] -> Left $ constructTIError p "could not infer concrete type of equation"
    







  
