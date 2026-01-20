module Utils.Misc where

consIf :: Bool -> a -> [a] -> [a]
consIf True x xs = x:xs
consIf False _ xs = xs
