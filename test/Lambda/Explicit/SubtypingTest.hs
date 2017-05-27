{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Lambda.Explicit.SubtypingTest where

import Test.Tasty
import Test.Tasty.HUnit
import Preliminary.Types
import Expr.Arith
import Lambda.Explicit.Simply
import Lambda.Explicit.Subtyping

typeofTests = testGroup "typeof" $
  [ testCase "|- (λ(0:{x:nat}). 0.x) {x=0, y=true} : nat" $
    typeof' @"subcontext" (sabs 0 (record [("x", nat)]) (proj (svar 0) "x") `sapp` fields [("x", azero), ("y", atrue)]) @?= Just nat
  ]

mainTests =
  [ typeofTests
  ]


