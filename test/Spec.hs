import Test.Tasty
import AExpTest
import UntypedTest
import SimplyTest
import SimplyExtTest
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "AExp" aexpTests
  , testGroup "Untyped" untypedTests
  , testGroup "Simply" simplyTests
  , testGroup "SimplyExt" simplyExtTests
--  testGroup "Mu" muTests,
--  testGroup "Recursive" recursiveTests
  ]
