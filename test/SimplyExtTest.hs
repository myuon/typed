{-# LANGUAGE TypeApplications #-}
module SimplyExtTest where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Init
import AExp
import Simply
import SimplyExt

typeofTests = testGroup "typeof"
  [ testCase "|- λ0:A. 0 : A -> A" $
    typeof @(Context Syntax -> Syntax) (sabs 0 baseA (svar 0)) M.empty @?= baseA `arrow` baseA
  , testCase "|- λ0:(A -> A). λ1:A. 0 1 : (A -> A) -> A -> A" $
    typeof @(Context Syntax -> Syntax) (sabs 0 (baseA `arrow` baseA) (sabs 1 baseA (svar 0 `sapp` svar 1))) M.empty @?= (baseA `arrow` baseA) `arrow` (baseA `arrow` baseA)
  , testCase "|- * : unit" $
    typeof @(Context Syntax -> Syntax) star M.empty @?= unit
  , testCase "|- λ(0:A -> unit). λ(1:A). 0 1 ## 0 : (A -> unit) -> A -> A -> unit" $
    typeof @(Context Syntax -> Syntax) (sabs 0 (baseA `arrow` unit) (sabs 1 baseA ((svar 0 `sapp` svar 1) ## svar 0))) M.empty @?= (baseA `arrow` unit) `arrow` (baseA `arrow` (baseA `arrow` unit))
  ]

simplyExtTests =
  [ typeofTests
  ]
