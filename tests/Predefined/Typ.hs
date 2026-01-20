{-# LANGUAGE OverloadedStrings #-}

module Predefined.Typ where

import Typ.Type (Typ(..))

import qualified Predefined.Sort as Sort

a :: Typ
a = Typ [] Sort.a

b :: Typ
b = Typ [] Sort.b

aa :: Typ
aa = Typ [a] Sort.a

aaa :: Typ
aaa = Typ [a,a] Sort.a

aaToa :: Typ
aaToa = Typ [aa] Sort.a

bb :: Typ
bb = Typ [b] Sort.b

bbb :: Typ
bbb = Typ [b,b] Sort.b

ab :: Typ
ab = Typ [a] Sort.b

ba :: Typ
ba = Typ [b] Sort.a

abb :: Typ
abb = Typ [a,b] Sort.b
