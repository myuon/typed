import Test.Tasty
import AExpTest
import UntypedTest
import SimplyTest
import SimplyExtTest
import ReferenceTest
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "AExp" aexpTests
  , testGroup "Untyped" untypedTests
  , testGroup "Simply" simplyTests
  , testGroup "SimplyExt" simplyExtTests
  , testGroup "Reference" referenceTests
--  testGroup "Mu" muTests,
--  testGroup "Recursive" recursiveTests
  ]
