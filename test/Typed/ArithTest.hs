module Typed.ArithTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Arith

test_typeof =
  [ testCase "|- true : Bool" $ rights [typeof () (ArithTerm $ Ttrue)] @?= [Tbool]
  , testCase "|- if false then (pred 0) else (succ 0) : Nat" $ rights [typeof () (ArithTerm $ Tif Tfalse Tzero (Tsucc Tzero))] @?= [Tnat]
  ]

_test_eval =
  [
  ]

