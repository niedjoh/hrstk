{-# LANGUAGE OverloadedStrings #-}

module Predefined.Var where

import Utils.Type (Id(..),Var(..))
  
import Term (Head(..))

x :: Head
x = FV . Named . Id $ "x"

y :: Head
y = FV . Named . Id $ "y"

z :: Head
z = FV . Named . Id $ "z"

xp :: Head
xp = FV . Named . Id $ "x'"

yp :: Head
yp = FV . Named . Id $ "y'"

zp :: Head
zp = FV . Named . Id $ "z'"

fresh :: Int -> Head
fresh i = FV . Fresh $ i

fresh0 :: Head
fresh0 = fresh 0

fresh1 :: Head
fresh1 = fresh 1

fresh2 :: Head
fresh2 = fresh 2

fresh3 :: Head
fresh3 = fresh 3

