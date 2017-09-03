module Typed.SimplyTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Untyped.Arith
import Typed.Simply

test_typeof =
  [ testCase "|- if iszero 0 then 0 else pred 0 : Nat" $ rights [typeof @"simply" M.empty (Tif Ttrue (Tabs "x" Tbool (Tvar "x")) (Tabs "x" Tbool (Tvar "x")))] @?= [Tarr Tbool Tbool]
  , testCase "f:bool -> bool |- λx:bool. f (if x then false else x):bool -> bool" $ rights [typeof @"simply" (M.singleton "f" (VarBind (Tbool `Tarr` Tbool))) (Tabs "x" Tbool (Tvar "f" `Tapp` Tif (Tvar "x") Tfalse (Tvar "x")))] @?= [Tarr Tbool Tbool]
  ]

test_eval =
  [ testCase "(λx:bool. x) true" $ rights [eval @"simply" M.empty (Tabs "x" Tbool (Tvar "x") `Tapp` Ttrue)] @?= [Ttrue]
  ]

