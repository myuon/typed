module Typed.SubtypingTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Subtyping

test_typeof =
  [ testCase "|- λx:{hoge: Top}. x.hoge : {hoge: Top} -> Top"
  $ rights [typeof M.empty (SubtypeTerm $ Tabs "x" (Krecord [Kfield "hoge" Ktop]) (Tprojf "hoge" (Tvar "x")))]
  @?= [Krecord [Kfield "hoge" Ktop] `Karr` Ktop]
  , testCase "|- (λx:{hoge: Top -> Top}. x.hoge) {hoge = λx:Top.x, piyo = λx:Top.x} : Top -> Top" $ do
    r <- typeof M.empty (SubtypeTerm
      $ Tabs "x" (Krecord [Kfield "hoge" (Ktop `Karr` Ktop)]) (Tprojf "hoge" (Tvar "x"))
      `Tapp` Trecord [ Tfield "hoge" (Tabs "x" Ktop $ Tvar "x")
                     , Tfield "piyo" (Tabs "x" Ktop $ Tvar "x")])
    let s = Ktop `Karr` Ktop
    r @?= s
  ]
