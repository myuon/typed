module Typed.SimplyTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Simply

test_typeof =
  [ testCase "|- if iszero 0 then 0 else pred 0 : Nat" $ rights [typeof M.empty (SimplyTerm $ Tif Ttrue (Tabs "x" Tbool (Tvar "x")) (Tabs "x" Tbool (Tvar "x")))] @?= [Tarr Tbool Tbool]
  , testCase "f:bool -> bool |- λx:bool. f (if x then false else x):bool -> bool" $ rights [typeof (M.singleton "f" (VarBind (Tbool `Tarr` Tbool))) (SimplyTerm $ Tabs "x" Tbool (Tvar "f" `Tapp` Tif (Tvar "x") Tfalse (Tvar "x")))] @?= [Tarr Tbool Tbool]
  ]

test_eval =
  [ testCase "(λx:bool. x) true" $ rights [eval M.empty (SimplyTerm $ Tabs "x" Tbool (Tvar "x") `Tapp` Ttrue)] @?= [SimplyTerm Ttrue]
  , testCase "λx:bool. true" $ rights [eval M.empty (SimplyTerm $ Tabs "x" Tbool Ttrue)] @?= [SimplyTerm $ Tabs "x" Tbool Ttrue]
  ]

