module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Typed.Simply
import Typed.SimplyExt

test_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (Tabs "x" Tbase (Tvar "x"))] @?= [Tarr Tbase Tbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (Tabs "f" (Tbase `Tarr` Tbase) (Tabs "x" Tbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Tbase `Tarr` Tbase) `Tarr` (Tbase `Tarr` Tbase)]
  ]
