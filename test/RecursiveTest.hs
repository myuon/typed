module RecursiveTest (recursiveTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Either (isRight, isLeft)
import Control.Monad.Except
import Control.Monad.Catch.Pure
import Recursive

showTypTest = testGroup "show Typ" [
  testCase "?0 -> ?1 -> ?2" $
    show (hole 0 ~> hole 1 ~> hole 2) @?= "?0 -> ?1 -> ?2",
  testCase "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6" $
    show ((hole 0 ~> hole 1) ~> (hole 2 ~> hole 3 ~> hole 4) ~> hole 5 ~> hole 6) @?= "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6"
  ]

showExprTest = testGroup "show Expr" [
  testCase "λx. λy. xx(yx)" $
    show (lam "x" $ lam "y" $ var "x" <#> var "x" <#> (var "y" <#> var "x")) @?= "λx. λy. xx(yx)"
  ]

typingTest = testGroup "typing" [
  testCase "x : Fail" $
    typing (var "x") @?= Nothing,
  testCase "λx. λy. x y : (?0 -> ?1) -> ?0 -> ?1" $
    typing (lam "x" $ lam "y" $ var "x" <#> var "y") @?= Just ((hole 0 ~> hole 1) ~> hole 0 ~> hole 1),
  testCase "λx.x : ?0 -> ?0" $
    typing (lam "x" $ var "x") @?= Just ((Hole $ HoleId 0) ~> (Hole $ HoleId 0)),
  testCase "λx.x x : Fail" $
    typing (lam "x" $ var "x" <#> var "x") @?= Nothing,
  testCase "λfxy.f (y x) : (?0 -> ?1) -> ?2 -> (?2 -> ?0) -> ?1" $
    typing (lam "f" $ lam "x" $ lam "y" $ var "f" <#> (var "y" <#> var "x"))
    @?= Just ((hole 0 ~> hole 1) ~> hole 2 ~> (hole 2 ~> hole 0) ~> hole 1),
  testCase "λfxy.f x (f x y) : (?0 -> ?1 -> ?1) -> ?0 -> ?1 -> ?1" $
    typing (lam "f" $ lam "x" $ lam "y" $ var "f" <#> var "x" <#> (var "f" <#> var "x" <#> var "y"))
    @?= Just ((hole 0 ~> hole 1 ~> hole 1) ~> hole 0 ~> hole 1 ~> hole 1),
  testCase "λf. λx. f (f (f x)) : (?0 -> ?0) -> ?0 -> ?0" $
    typing (lam "f" $ lam "x" $ var "f" <#> (var "f" <#> (var "f" <#> var "x")))
    @?= Just ((hole 0 ~> hole 0) ~> hole 0 ~> hole 0)
  ]

typeCheckTest = testGroup "typeCheck" [
  ]

normalizeTest = testGroup "normalize" [
  ]

recursiveTests = [
  showTypTest,
  showExprTest,
  typingTest,
  typeCheckTest,
  normalizeTest
  ]
