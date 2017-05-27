{-# LANGUAGE TypeApplications #-}
module Lambda.Explicit.UntypedTest where

import Test.Tasty
import Test.Tasty.HUnit
import Preliminary.Types
import Lambda.Explicit.Untyped

cbvTests = testGroup "cbv" $
  [ testCase "(λ. 1 0 2) (λ. 0) ~> 0 (λ. 0) 1"
    $ cbv (uabs (uvar 1 `uapp` uvar 0 `uapp` uvar 2) `uapp` (uabs (uvar 0))) @?= (uvar 0 `uapp` (uabs (uvar 0)) `uapp` uvar 1)
  , testCase "(λ. 0 0) (λ. 0) ~> (λ. 0)"
    $ cbv (uabs (uvar 0 `uapp` uvar 0) `uapp` (uabs (uvar 0))) @?= (uabs (uvar 0))
  ]

mainTests =
  [ cbvTests
  ]


