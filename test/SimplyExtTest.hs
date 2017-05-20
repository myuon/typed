{-# LANGUAGE TypeApplications #-}
module SimplyExtTest where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Init
import AExp
import Simply
import SimplyExt

infer = inferSpExt @Int @Syntax @Syntax

inferTests = testGroup "infer"
  [ testCase "|- λ0:A. 0 : A -> A" $
    infer M.empty (sabs 0 baseA (svar 0)) @?= baseA `arrow` baseA
  , testCase "|- λ0:(A -> A). λ1:A. 0 1 : (A -> A) -> A -> A" $
    infer M.empty (sabs 0 (baseA `arrow` baseA) (sabs 1 baseA (svar 0 `sapp` svar 1))) @?= (baseA `arrow` baseA) `arrow` (baseA `arrow` baseA)
  , testCase "|- * : unit" $
    infer M.empty star @?= unit
  , testCase "|- λ(0:A -> unit). λ(1:A). 0 1 ## 0 : A -> unit" $
    infer M.empty (sabs 0 (baseA `arrow` unit) (sabs 1 baseA ((svar 0 `sapp` svar 1) ## svar 0))) @?= baseA `arrow` unit
  ]
  
simplyExtTests =
  [ inferTests
  ]
