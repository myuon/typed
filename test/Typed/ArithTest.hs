module Typed.ArithTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Arith

test_typeof =
  [ testCase "|- true : Bool" $ rights [typeof () (ArithTerm $ Ttrue)] @?= [Kbool]
  , testCase "|- if false then (pred 0) else (succ 0) : Nat" $ rights [typeof () (ArithTerm $ Tif Tfalse Tzero (Tsucc Tzero))] @?= [Knat]
  ]

test_eval =
  [ testCase "if true then iszero (pred (succ 0)) else false -> true" $ rights [eval () (ArithTerm $ Tif Ttrue (Tiszero (Tpred (Tsucc Tzero))) Tfalse)] @?= [ArithTerm Ttrue]
  , testCase "iszero (succ (pred 0)) -> false" $ rights [eval () (ArithTerm $ Tiszero (Tsucc (Tpred Tzero)))] @?= [ArithTerm Tfalse]
  ]

