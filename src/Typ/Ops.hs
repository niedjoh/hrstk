-- |Collection of useful functions for simple types
module Typ.Ops where

import Data.Set (Set)
import qualified Data.Set as S

import Utils.Type (Id(..))
import Typ.Type (Typ(..))

-- |Checks whether a type is a sort.
sort :: Typ -> Bool
sort (Typ [] _) = True
sort _ = False

-- |Yields the argument types of a given type.
argTyps :: Typ -> [Typ]
argTyps (Typ as _) = as

-- |Yields the return sort of a given type.
returnSort :: Typ -> Id
returnSort (Typ _ a) = a

-- |Yields the return type of a given type.
returnTyp :: Typ -> Typ
returnTyp (Typ _ a) = Typ [] a

-- |Lifts a given typ to a functional context.
liftTyp :: [Typ] -> Typ -> Typ
liftTyp as (Typ bs b) = Typ (as ++ bs) b

-- |Arity of a given type.
arity :: Typ -> Int
arity (Typ as _) = length as

-- |Determine the order of a given type.
order :: Typ -> Int
order (Typ [] _) = 1
order (Typ as _) = maximum (1 : map ((+1) . order) as)

-- |Same as 'applTyp' but for multiple applications.
applyTyps :: Typ -> [Typ] -> Maybe Typ
applyTyps a [] = Just a
applyTyps (Typ (a:as) b) (c:cs) = if a == c
  then applyTyps (Typ as b) cs
  else Nothing
applyTyps _ _ = Nothing

-- |Determines whether the second type is equatable to the first type by applications.
-- If successful, a list of the types which need to be applied in order to get the
-- same type is returned.
equatableByTypApp :: Typ -> Typ -> Maybe [Typ]
equatableByTypApp (Typ as a) (Typ bs b) = go (Typ [] a : reverse as) (Typ [] b : reverse bs) where
  go [] [] = Just []
  go (_:_) [] = Nothing
  go (x:xs) (y:ys) = if x == y then go xs ys else Nothing
  go [] ys = Just (reverse ys)

-- |Set of sort positions in a type.
pos :: Typ -> Set [Int]
pos (Typ [] _) = S.singleton []
pos (Typ as _) = S.unions ( S.singleton [length as + 1]
                          : map (\(a,i) -> S.mapMonotonic (i:) (pos a)) (zip as [1..])
                          )
             
-- |Set of positions of a given basetype name in a type.
posOf :: Id -> Typ -> Set [Int]
posOf a (Typ [] b)
  | a == b    = S.singleton []
  | otherwise = S.empty
posOf a (Typ as b)
  | a == b    = S.unions (S.singleton [length as + 1] : recRess)
  | otherwise = S.unions recRess
  where
    recRess = map (\(c,i) -> S.mapMonotonic (i:) (posOf a c)) (zip as [1..])

-- |Set of positive base type positions in a type.
posPos :: Typ -> Set [Int]
posPos (Typ [] _) = S.singleton []
posPos (Typ as _) = S.unions ( S.singleton [length as + 1]
                             : map (\(a,i) -> S.mapMonotonic (i:) (posNeg a)) (zip as [1..])
                             )

-- |Set of negative base type positions in a type.
posNeg :: Typ -> Set [Int]
posNeg (Typ [] _) = S.empty
posNeg (Typ as _) = S.unions (map (\(a,i) -> S.mapMonotonic (i:) (posPos a)) (zip as [1..]))
