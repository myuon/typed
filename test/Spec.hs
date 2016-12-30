import Test.Tasty
import SimplyTest
import MuTest
import RecursiveTest

main :: IO ()
main = defaultMain $ testGroup "Tests" [
  testGroup "Simply" simplyTests,
  testGroup "Mu" muTests,
  testGroup "Recursive" recursiveTests
  ]
