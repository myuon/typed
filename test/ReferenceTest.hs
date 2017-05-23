{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module ReferenceTest where

import Test.Tasty
import Test.Tasty.HUnit
import GHC.TypeLits
import qualified Data.Map as M
import Init
import AExp
import Simply
import Reference

reftypeofTests = testGroup "reftypeof"
  [ testCase "|- ref 1 : Ref nat" $
    typeof' @"store" (ref (asucc azero)) @?= Just (reftype nat)
  , testCase "|- r := true; !r : bool" $
    typeof @"store" M.empty (M.singleton "r" bool) (assign (loc "r") atrue ## deref (loc "r")) @?= Just bool
  , testCase "|- λ0:Ref (nat -> nat). λ1:nat. !0 1 : Ref (nat -> nat) -> nat -> nat" $ typeof @"store" M.empty (M.singleton "0" (nat `arrow` nat)) (sabs 0 (reftype $ nat `arrow` nat) $ sabs 1 nat $ (deref $ loc "0") `sapp` svar 1) @?= Just (reftype (nat `arrow` nat) `arrow` (nat `arrow` nat))
  ]

mainTests =
  [ reftypeofTests
  ]

