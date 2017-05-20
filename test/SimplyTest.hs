{-# LANGUAGE TypeApplications #-}
module SimplyTest where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as M
import Init
import AExp
import Simply

typeofTests = testGroup "typeof"
  [ testCase "0 : bool |- 0 : bool" $
    typeof @(Context Syntax -> Syntax) (svar 0) (M.singleton 0 (VarBind bool)) @?= bool
  , testCase "|- λ0:(nat -> bool). λ1:nat. 0 1 : (nat -> bool) -> nat -> bool" $
    typeof @(Context Syntax -> Syntax) (sabs 0 (arrow nat bool) $ sabs 1 nat $ svar 0 `sapp` svar 1) M.empty @?= (nat `arrow` bool) `arrow` (nat `arrow` bool)
  , testCase "|- λ0:(bool -> bool). 0 : (bool -> bool) -> (bool -> bool)" $
    typeof @(Context Syntax -> Syntax) (sabs 0 (arrow bool bool) $ svar 0) M.empty @?= (bool `arrow` bool) `arrow` (bool `arrow` bool)
  ]
  
simplyTests =
  [ typeofTests
  ]
