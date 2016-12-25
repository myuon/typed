module MuTest (muTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Either (isLeft)
import Mu

showTypTest = testGroup "show Typ" [
  testCase "?0 -> ?1 -> ?2" $
    show (hole 0 ~> hole 1 ~> hole 2) @?= "?0 -> ?1 -> ?2",
  testCase "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6" $
    show ((hole 0 ~> hole 1) ~> (hole 2 ~> hole 3 ~> hole 4) ~> hole 5 ~> hole 6) @?= "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6"
  ]

showExprTest = testGroup "show Expr" [
  testCase "λx. λy. xx(yx)" $
    show (Lambda (VarId "x") (Lambda (VarId "y") $ App (App (var "x") (var "x")) (App (var "y") (var "x")))) @?= "λx. λy. xx(yx)",
  testCase "μα. [β] λy. y" $
    show (Mu (CtrlId "α") (Name (CtrlId "β") (Lambda (VarId "y") $ var "y"))) @?= "μα. [β] λy. y"
  ]

typeCheckTest = testGroup "typeCheck" [
  testCase "x : Fail" $
    isLeft (typeCheck (var "x")) @?= True,
  testCase "λx. λy. x y : (?0 -> ?1) -> ?0 -> ?1" $
    typeCheck (Lambda (VarId "x") $ Lambda (VarId "y") $ App (var "x") (var "y")) @?= Right ((hole 0 ~> hole 1) ~> hole 0 ~> hole 1),
  testCase "λx.x : ?0 -> ?0" $
    typeCheck (Lambda (VarId "x") (var "x")) @?= Right ((Hole $ HoleId 0) ~> (Hole $ HoleId 0)),
  testCase "λx.x x : Fail" $
    isLeft (typeCheck (Lambda (VarId "x") (App (var "x") (var "x")))) @?= True,
  testCase "λfxy.f (y x) : (?0 -> ?1) -> ?2 -> (?2 -> ?0) -> ?1" $
    typeCheck (Lambda (VarId "f") $ Lambda (VarId "x") $ Lambda (VarId "y") $ App (var "f") (App (var "y") (var "x")))
    @?= Right ((hole 0 ~> hole 1) ~> hole 2 ~> (hole 2 ~> hole 0) ~> hole 1),
  testCase "λfxy. f x (f x y) : (?0 -> ?1 -> ?1) -> ?0 -> ?1 -> ?1" $
    typeCheck (Lambda (VarId "f") $ Lambda (VarId "x") $ Lambda (VarId "y") $ App (App (var "f") (var "x")) (App (App (var "f") (var "x")) (var "y")))
    @?= Right ((hole 0 ~> hole 1 ~> hole 1) ~> hole 0 ~> hole 1 ~> hole 1)
  ]

typeCheckMuTest = testGroup "typeCheck mu" [
  testCase "μα. [α](λx. x) : ?0 -> ?0" $
    typeCheck (mu "a" $ name "a" $ lam "x" $ var "x") @?= Right (hole 0 ~> hole 0),
  testCase "callCC := λf. μα. f (λx. [α]x) : ((?0 -> _|_) -> _|_) -> ?0" $
    typeCheck callCC @?= Right (((hole 0 ~> Bottom) ~> Bottom) ~> hole 0),
  testCase "λa f. callCC (λg. f a) : ?0 -> (?0 -> ?1 -> _|_) -> ?1" $
    typeCheck (lam "a2" $ lam "f2" $ callCC <#> (lam "g" $ var "f2" <#> var "a2"))
    @?= Right (hole 0 ~> (hole 0 ~> hole 1 ~> Bottom) ~> hole 1)
  ]
  where
    -- callCC : ((A -> _|_) -> _|_) -> A
    callCC = lam "f" $ mu "a" $ var "f" <#> (lam "x" $ name "a" $ var "x")

    -- A \/ B == (A -> _|_) -> B
    -- ???

muTests = [
  showTypTest,
  showExprTest,
  typeCheckTest,
  typeCheckMuTest
  ]
