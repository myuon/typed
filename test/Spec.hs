import Test.Tasty
import AExpTest
import UntypedTest
import SimplyTest
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "UnAExp" aexpTests
  , testGroup "Untyped" untypedTests
--  testGroup "Simply" simplyTests,
--  testGroup "Mu" muTests,
--  testGroup "Recursive" recursiveTests
  ]
