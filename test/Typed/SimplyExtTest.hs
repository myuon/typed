module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.SimplyExt

test_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "x" Tbase (Tvar "x"))] @?= [Tarr Tbase Tbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "f" (Tbase `Tarr` Tbase) (Tabs "x" Tbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Tbase `Tarr` Tbase) `Tarr` (Tbase `Tarr` Tbase)]
  ]

{-
_test_eval =
  [ testCase "(λf:unit -> unit. f *) (λx:unit. x) -> *" $ rights [eval M.empty (SimplyExtTerm $ Tabs "f" (Tunit `Tarr` Tunit) (Tvar "f" `Tapp` Tstar) `Tapp` (Tabs "x" Tunit (Tvar "x")))] @?= [SimplyExtTerm Tstar]
  ]
-}

