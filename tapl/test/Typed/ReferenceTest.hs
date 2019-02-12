module Typed.ReferenceTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Reference

test_eval =
  [ testCase "! (ref unit) -> unit" $ rights [fmap (\(RefEvalTerm t mu) -> t) $ evalext $ RefEvalTerm (Tderef (Tref Tunit)) (M.singleton "*" (Tval "_"))] @?= [Tunit]
  ]

test_tyepof =
  [ testCase "|- ! (ref unit) : unit" $ rights [typeof (M.empty,M.empty) $ ReferenceTerm $ Tderef (Tref Tunit)] @?= [Kunit]
  ]

