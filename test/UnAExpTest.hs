{-# LANGUAGE TypeApplications #-}
module UnAExpTest where

import Test.Tasty
import Test.Tasty.HUnit
import UnAExp

aevalTests = testGroup "aeval" $
  [ testCase "if true then 0 else 1 ~> 0"
    $ aeval @Syntax @AValue (aif atrue azero (asucc azero)) @?= azero
  , testCase "if false then 0 else 1 ~> 1"
    $ aeval @Syntax @AValue (aif afalse azero (asucc azero)) @?= asucc azero
  , testCase "if (iszero 1) then 0 else 1 ~> 1"
    $ aeval @Syntax @AValue (aif (aisZero (asucc azero)) azero (asucc azero)) @?= asucc azero
  , testCase "succ (pred (succ (pred 0))) ~> 1"
    $ aeval @Syntax @AValue (asucc $ apred $ asucc $ apred azero) @?= asucc azero
  , testCase "if true then true else (if false then false else false) ~> true"
    $ aeval @Syntax @AValue (aif atrue atrue (aif afalse afalse afalse)) @?= atrue
  ]

aexpTests =
  [ aevalTests
  ]


