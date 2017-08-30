module ArithTest where

import Data.Either
import Test.Tasty.HUnit
import Untyped.Arith

test_eval =
  [ testCase "if true true (if false false false) -> true" $ rights [eval (Tif Ttrue Ttrue (Tif Tfalse Tfalse Tfalse))] @?= [Ttrue]
  ]


