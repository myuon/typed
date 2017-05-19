import Test.Tasty
import UnAExpTest
import SimplyTest
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "UnAExp" aexpTests
--  testGroup "Simply" simplyTests,
--  testGroup "Mu" muTests,
--  testGroup "Recursive" recursiveTests
  ]
