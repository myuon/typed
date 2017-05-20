{-# LANGUAGE TypeApplications #-}
module SimplyTest where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Init
import AExp
import Simply

infer = inferSp @Int @Syntax @Syntax

inferTests = testGroup "infer"
  [ testCase "0 : bool |- 0 : bool" $
    infer (M.singleton "0" (VarBind bool)) (svar 0) @?= bool
  , testCase "|- λ0:(nat -> bool). λ1:nat. 0 1 : (nat -> bool) -> nat -> bool" $
    infer M.empty (sabs 0 (arrow nat bool) $ sabs 1 nat $ svar 0 `sapp` svar 1) @?= (nat `arrow` bool) `arrow` (nat `arrow` bool)
  , testCase "|- λ0:(bool -> bool). 0 : (bool -> bool) -> (bool -> bool)" $
    infer M.empty (sabs 0 (arrow bool bool) $ svar 0) @?= (bool `arrow` bool) `arrow` (bool `arrow` bool)
  ]
  
simplyTests =
  [ inferTests
  ]
