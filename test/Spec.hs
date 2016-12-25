import Test.Tasty
import MuTest

main :: IO ()
main = defaultMain $ testGroup "Tests" [
  testGroup "Mu" muTests
  ]
