{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Untyped.ArithTest where

import Data.Either
import Test.Tasty.HUnit
import Untyped.Arith
import Preliminaries

test_eval =
  [ testCase "if true true (if false false false) -> true" $ rights [eval () (ArithTerm $ Tif Ttrue Ttrue (Tif Tfalse Tfalse Tfalse))] @?= [ArithTerm Ttrue]
  ]


