module Typed.ArithTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Untyped.Arith hiding (ArithTerm)
import Typed.Arith

test_typeof =
  [ testCase "|- true : Bool" $ rights [typeof () (ArithTerm $ Ttrue)] @?= [Tbool]
  ]

_test_eval =
  [
  ]

