module MuTest (muTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Either (isLeft, isRight)
import Mu

showTypTest = testGroup "show Typ" [
  testCase "?0 -> ?1 -> ?2" $
    show (hole 0 ~> hole 1 ~> hole 2) @?= "?0 -> ?1 -> ?2",
  testCase "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6" $
    show ((hole 0 ~> hole 1) ~> (hole 2 ~> hole 3 ~> hole 4) ~> hole 5 ~> hole 6) @?= "(?0 -> ?1) -> (?2 -> ?3 -> ?4) -> ?5 -> ?6"
  ]

showExprTest = testGroup "show Expr" [
  testCase "λx. λy. xx(yx)" $
    show (lam "x" $ lam "y" $ var "x" <#> var "x" <#> (var "y" <#> var "x")) @?= "λx. λy. xx(yx)",
  testCase "μα. [β] λy. y" $
    show (mu "α" $ name "β" $ lam "y" $ var "y") @?= "μα. [β] λy. y"
  ]

typingTest = testGroup "typing" [
  testCase "x : Fail" $
    isLeft (typing (var "x")) @?= True,
  testCase "λx. λy. x y : (?0 -> ?1) -> ?0 -> ?1" $
    typing (lam "x" $ lam "y" $ var "x" <#> var "y") @?= Right ((hole 0 ~> hole 1) ~> hole 0 ~> hole 1),
  testCase "λx.x : ?0 -> ?0" $
    typing (lam "x" $ var "x") @?= Right ((Hole $ HoleId 0) ~> (Hole $ HoleId 0)),
  testCase "λx.x x : Fail" $
    isLeft (typing (lam "x" $ var "x" <#> var "x")) @?= True,
  testCase "λfxy.f (y x) : (?0 -> ?1) -> ?2 -> (?2 -> ?0) -> ?1" $
    typing (lam "f" $ lam "x" $ lam "y" $ var "f" <#> (var "y" <#> var "x"))
    @?= Right ((hole 0 ~> hole 1) ~> hole 2 ~> (hole 2 ~> hole 0) ~> hole 1),
  testCase "λfxy.f x (f x y) : (?0 -> ?1 -> ?1) -> ?0 -> ?1 -> ?1" $
    typing (lam "f" $ lam "x" $ lam "y" $ var "f" <#> var "x" <#> (var "f" <#> var "x" <#> var "y"))
    @?= Right ((hole 0 ~> hole 1 ~> hole 1) ~> hole 0 ~> hole 1 ~> hole 1)
  ]

callCC = lam "f" $ mu "a" $ var "f" <#> lam "x" (name "a" $ var "x")

andT a b = (a ~> b ~> Bottom) ~> Bottom
proj1 = lam "f" $ mu "alpha" $ var "f" <#> (lam "a" $ lam "b" $ name "alpha" $ var "a")
proj2 = lam "f" $ mu "beta" $ var "f" <#> (lam "a" $ lam "b" $ name "beta" $ var "b")
mkPair = lam "a" $ lam "b" $ lam "f" $ var "f" <#> var "a" <#> var "b"

orT a b = (a ~> Bottom) ~> (b ~> Bottom) ~> Bottom
inj1 = lam "a" $ lam "f" $ lam "g" $ var "f" <#> var "a"
inj2 = lam "b" $ lam "f" $ lam "g" $ var "g" <#> var "b"
ite = lam "ab" $ lam "f" $ lam "g" $ callCC <#> (lam "h" $ var "ab" <#> (lam "a" $ var "h" <#> (var "f" <#> var "a")) <#> (lam "b" $ var "h" <#> (var "g" <#> var "b")))

boolean = Bottom ~> Bottom ~> Bottom
true = lam "x" $ lam "y" $ var "x"
false = lam "x" $ lam "y" $ var "y"

nat = Bottom ~> (Bottom ~> Bottom) ~> Bottom
zero = lam "z" $ lam "s" $ var "z"
suc = lam "n" $ lam "z" $ lam "s" $ var "s" <#> (var "n" <#> var "z" <#> var "s")
-- nat -> C -> (nat -> C -> C) -> C
--prim = lam "n" $ lam "g0" $ lam "gs" $ callCC <#> (lam "k" $ var "n" <#> (var "k" <#> var "g0") <#> (lam "p" $ var "k" <#> (var "gs" <#> var "n" <#> )))

typingMuTest = testGroup "typing" [
  testCase "μα. [α](λx. x) : ?0 -> ?0" $
    typing (mu "a" $ name "a" $ lam "x" $ var "x") @?= Right (hole 0 ~> hole 0),
  testCase "callCC := λf. μα. f (λx. [α]x) : ¬¬?0 -> ?0" $
    typing callCC @?= Right (((hole 0 ~> Bottom) ~> Bottom) ~> hole 0),
  testCase "proj1 := λf. μα. f (λa. λb. [α] a) : ?0 /\\ ?1 -> ?0" $
    typing proj1 @?= Right (andT (hole 0) (hole 1) ~> hole 0),
  testCase "proj2 := λf. μα. f (λa. λb. [α] b) : ?0 /\\ ?1 -> ?1" $
    typing proj2 @?= Right (andT (hole 0) (hole 1) ~> hole 1),
  testCase "mkPair := λa. λb. λf. f a b : ?0 -> ?1 -> ?0 /\\ ?1" $
    typing mkPair @?= Right (hole 0 ~> hole 1 ~> (hole 0 ~> hole 1 ~> hole 2) ~> hole 2)
  ]

typeCheckTest = testGroup "typeCheck" [
  testCase "mkPair := λa. λb. λf. f a b : ?0 -> ?1 -> ?0 /\\ ?1" $
    isRight (typeCheck mkPair (hole 0 ~> hole 1 ~> andT (hole 0) (hole 1))) @?= True,
  testCase "inj1 := λa. λf. λg. f a : ?0 -> ?0 \\/ ?1" $
    isRight (typeCheck inj1 (hole 0 ~> orT (hole 0) (hole 1))) @?= True,
  testCase "ite := λab. λf. λg. callCC (λh. ab (λa. h (f a)) (λb. h (g b))) : ?0 \\/ ?1 -> (?0 -> ?2) -> (?1 -> ?2) -> ?2" $
    isRight (typeCheck ite (orT (hole 0) (hole 1) ~> (hole 0 ~> hole 2) ~> (hole 1 ~> hole 2) ~> hole 2)) @?= True,
  testCase "true : boolean" $
    isRight (typeCheck true boolean) @?= True,
  testCase "suc (suc zero) : nat" $
    isRight (typeCheck (suc <#> (suc <#> zero)) nat) @?= True
  ]

normalizeTest = testGroup "normalize" [
  testCase "proj1 (mkPair M N) = M" $
    normalize (lam "M" $ lam "N" $ proj1 <#> (mkPair <#> var "M" <#> var "N")) @?= (lam "M" $ lam "N" $ var "M"),
--  testCase "mkPair (proj1 M) (proj2 M) = M" $
--    normalize (lam "M" $ mkPair <#> (proj1 <#> var "M") <#> (proj2 <#> var "M")) @?= (lam "M" $ var "M")
  testCase "ite (inj1 M) f g = f M" $
    normalize (lam "M" $ lam "f" $ lam "g" $ ite <#> (inj1 <#> var "M") <#> var "f" <#> var "g") @?= (lam "M" $ lam "f" $ lam "g" $ var "f" <#> var "M"),
  testCase "inj1 (ite ab f g) = g N" $
    normalize (lam "N" $ lam "f" $ lam "g" $ ite <#> (inj2 <#> var "N") <#> var "f" <#> var "g") @?= (lam "N" $ lam "f" $ lam "g" $ var "g" <#> var "N")
  ]

muTests = [
  showTypTest,
  showExprTest,
  typingTest,
  typingMuTest,
  typeCheckTest,
  normalizeTest
  ]
