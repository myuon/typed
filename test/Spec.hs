import Test.Tasty
import Expr.ArithTest as A
import Lambda.Explicit.UntypedTest as U
import Lambda.Explicit.SimplyTest as S
import Lambda.Explicit.SimplyExtTest as SE
import Lambda.Explicit.ReferenceTest as R
import Lambda.Explicit.ExceptionTest as E
import Lambda.Explicit.SubtypingTest as SB
import Lambda.Explicit.RecursiveTest as RC
-- import MuTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "Arith" A.mainTests
  , testGroup "Untyped" U.mainTests
  , testGroup "Simply" S.mainTests
  , testGroup "SimplyExt" SE.mainTests
  , testGroup "Reference" R.mainTests
  , testGroup "Exception" E.mainTests
  , testGroup "Subtyping" SB.mainTests
  , testGroup "Recursive" RC.mainTests
--  testGroup "Mu" muTests,
  ]
