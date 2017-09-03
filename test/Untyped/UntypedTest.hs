{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Untyped.UntypedTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Untyped.Untyped

test_eval =
  [ testCase "(λ. 1 0 2) (λ. 0) -> 0 (λ. 0) 1" $ rights [eval @_ @"untyped" undefined M.empty (Tabs (Tvar "1" `Tapp` Tvar "0" `Tapp` Tvar "2") `Tapp` Tabs (Tvar "0"))] @?= [Tvar "0" `Tapp` (Tabs (Tvar "0")) `Tapp` Tvar "1"]
  ]

