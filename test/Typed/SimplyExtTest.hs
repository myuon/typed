module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Typed.Simply hiding (eval)
import Typed.SimplyExt

{-
est_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (Tabs "x" Tbase (Tvar "x"))] @?= [Tarr Tbase Tbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (Tabs "f" (Tbase `Tarr` Tbase) (Tabs "x" Tbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Tbase `Tarr` Tbase) `Tarr` (Tbase `Tarr` Tbase)]
  ]

est_eval =
  [ testCase "(λf:unit -> unit. f *) (λx:unit. x) -> *" $ rights [eval M.empty (Tabs "f" (Tunit `Tarr` Tunit) (Tvar "f" `Tapp` Tstar) `Tapp` (Tabs "x" Tunit (Tvar "x")))] @?= [Tstar]
  ]

-}
