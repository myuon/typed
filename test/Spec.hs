import Test.Tasty
import SimplyTest
import MuTest

main :: IO ()
main = defaultMain $ testGroup "Tests" [
  testGroup "Simply" simplyTests,
  testGroup "Mu" muTests
  ]
