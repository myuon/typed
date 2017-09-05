module Typed.SimplyTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.Simply

test_typeof =
  [ testCase "|- if iszero 0 then 0 else pred 0 : Nat" $ rights [typeof M.empty (SimplyTerm $ Tif Ttrue (Tabs "x" Kbool (Tvar "x")) (Tabs "x" Kbool (Tvar "x")))] @?= [Karr Kbool Kbool]
  , testCase "f:bool -> bool |- λx:bool. f (if x then false else x):bool -> bool" $ rights [typeof (M.singleton "f" (VarBind (Kbool `Karr` Kbool))) (SimplyTerm $ Tabs "x" Kbool (Tvar "f" `Tapp` Tif (Tvar "x") Tfalse (Tvar "x")))] @?= [Karr Kbool Kbool]
  ]

test_eval =
  [ testCase "(λx:bool. x) true" $ rights [eval M.empty (SimplyTerm $ Tabs "x" Kbool (Tvar "x") `Tapp` Ttrue)] @?= [SimplyTerm Ttrue]
  , testCase "λx:bool. true" $ rights [eval M.empty (SimplyTerm $ Tabs "x" Kbool Ttrue)] @?= [SimplyTerm $ Tabs "x" Kbool Ttrue]
  ]

