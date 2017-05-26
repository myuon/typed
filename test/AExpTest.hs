{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module AExpTest where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Init
import AExp

cbvTests = testGroup "cbv" $
  [ testCase "if true then 0 else 1 ~> 0"
    $ cbv (aif atrue azero (asucc azero)) @?= azero
  , testCase "if false then 0 else 1 ~> 1"
    $ cbv (aif afalse azero (asucc azero)) @?= asucc azero
  , testCase "if (iszero 1) then 0 else 1 ~> 1"
    $ cbv (aif (aisZero (asucc azero)) azero (asucc azero)) @?= asucc azero
  , testCase "succ (pred (succ (pred 0))) ~> 1"
    $ cbv (asucc $ apred $ asucc $ apred azero) @?= asucc azero
  , testCase "if true then true else (if false then false else false) ~> true"
    $ cbv (aif atrue atrue (aif afalse afalse afalse)) @?= atrue
  ]

typeofTests = testGroup "typeof" $
  [ testCase "if iszero 0 then 0 else pred 0 : nat"
    $ typeof' @"context" (aif (aisZero azero) azero (apred azero)) @?= Just Pnat
  , testCase "iszero (succ (succ 0)) : bool"
    $ typeof' @"context" (aisZero (asucc (asucc azero))) @?= Just Pbool
  ]

mainTests =
  [ cbvTests
  , typeofTests
  ]


