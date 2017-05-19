{-# LANGUAGE TypeApplications #-}
module AExpTest where

import Test.Tasty
import Test.Tasty.HUnit
import AExp

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

inferTests = testGroup "infer" $
  [ testCase "if iszero 0 then 0 else pred 0 : nat"
    $ infer @Syntax (aif (aisZero azero) azero (apred azero)) @?= Pnat
  , testCase "iszero (succ (succ 0)) : bool"
    $ infer @Syntax (aisZero (asucc (asucc azero))) @?= Pbool
  ]

aexpTests =
  [ aevalTests
  , inferTests
  ]


