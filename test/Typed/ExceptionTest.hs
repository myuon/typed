module Typed.ExceptionTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Exception

test_typeof =
  [ testCase "|- (λx:bool. true) error" $ rights [typeof M.empty (ExceptionTerm $ Tapp (Tabs "x" Kbool Ttrue) (Terroras Kbool))] @?= [Kbool]
  ]

test_eval =
  [ testCase "(λx:bool. true) error -> error" $ rights [eval (ExceptionTerm $ Tapp (Tabs "x" Kbool Ttrue) (Terroras Kbool))] @?= [ExceptionTerm (Terroras Kbool)]
  ]

