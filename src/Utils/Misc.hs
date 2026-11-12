module Utils.Misc where

import Control.Applicative (Alternative,(<|>))

consIf :: Bool -> a -> [a] -> [a]
consIf True x xs = x:xs
consIf False _ xs = xs

fst4 :: (a,b,c,d) -> a
fst4 (x,_,_,_) = x

allPossibilities :: [[a]] -> [[a]]
allPossibilities [] = [[]]
allPossibilities (xs:xss) = concat [map (x:) (allPossibilities xss) | x <- xs]

someIterations :: (Monad m, Alternative m) => (a -> m a) -> a -> m a
someIterations v = some_v where
  many_v x = some_v x <|> pure x
  some_v x = do
    y <- v x
    many_v y
