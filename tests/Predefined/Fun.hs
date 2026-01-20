{-# LANGUAGE OverloadedStrings #-}

module Predefined.Fun where

import Utils.Type (Id(..))
  
import Term (Head(..))

c :: Head
c = F . Id $ "c"

d :: Head
d = F . Id $ "d"

f :: Head
f = F . Id $ "f"

g :: Head
g = F . Id $ "g"

h :: Head
h = F . Id $ "h"
