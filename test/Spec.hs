import Test.Tasty
import AExpTest as A
import UntypedTest as U
import SimplyTest as S
import SimplyExtTest as SE
import ReferenceTest as R
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "AExp" A.mainTests
  , testGroup "Untyped" U.mainTests
  , testGroup "Simply" S.mainTests
  , testGroup "SimplyExt" SE.mainTests
  , testGroup "Reference" R.mainTests
--  testGroup "Mu" muTests,
--  testGroup "Recursive" recursiveTests
  ]
