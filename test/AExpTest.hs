{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module AExpTest where

import Test.Tasty
import Test.Tasty.HUnit
import Init
import AExp

aevalTests = testGroup "aeval" $
  [ testCase "if true then 0 else 1 ~> 0"
    $ aeval (aif atrue azero (asucc azero)) @?= azero
  , testCase "if false then 0 else 1 ~> 1"
    $ aeval (aif afalse azero (asucc azero)) @?= asucc azero
  , testCase "if (iszero 1) then 0 else 1 ~> 1"
    $ aeval (aif (aisZero (asucc azero)) azero (asucc azero)) @?= asucc azero
  , testCase "succ (pred (succ (pred 0))) ~> 1"
    $ aeval (asucc $ apred $ asucc $ apred azero) @?= asucc azero
  , testCase "if true then true else (if false then false else false) ~> true"
    $ aeval (aif atrue atrue (aif afalse afalse afalse)) @?= atrue
  ]

typeofTests = testGroup "typeof" $
  [ testCase "if iszero 0 then 0 else pred 0 : nat"
    $ typeof @"typecheck_simpl" (aif (aisZero azero) azero (apred azero)) @?= Pnat
  , testCase "iszero (succ (succ 0)) : bool"
    $ typeof @"typecheck_simpl" (aisZero (asucc (asucc azero))) @?= Pbool
  ]

aexpTests =
  [ aevalTests
  , typeofTests
  ]


