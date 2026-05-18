module Utils.Misc where

consIf :: Bool -> a -> [a] -> [a]
consIf True x xs = x:xs
consIf False _ xs = xs

fst4 :: (a,b,c,d) -> a
fst4 (x,_,_,_) = x

allPossibilities :: [[a]] -> [[a]]
allPossibilities [] = [[]]
allPossibilities (xs:xss) = concat [map (x:) (allPossibilities xss) | x <- xs]

