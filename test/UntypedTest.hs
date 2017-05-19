{-# LANGUAGE TypeApplications #-}
module UntypedTest where

import Test.Tasty
import Test.Tasty.HUnit
import Untyped

uevalTests = testGroup "ueval" $
  [ testCase "(λ. 1 0 2) (λ. 0) ~> 0 (λ. 0) 1"
    $ ueval @Syntax (Pabs (Pvar "1" `Papp` Pvar "0" `Papp` Pvar "2") `Papp` (Pabs (Pvar "0"))) @?= (Pvar "0" `Papp` (Pabs (Pvar "0")) `Papp` Pvar "1")
  , testCase "(λ. 0 0) (λ. 0) ~> (λ. 0)"
    $ ueval @Syntax (Pabs (Pvar "0" `Papp` Pvar "0") `Papp` (Pabs (Pvar "0"))) @?= (Pabs (Pvar "0"))
  ]

untypedTests =
  [ uevalTests
  ]


