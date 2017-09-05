module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.SimplyExt

test_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "x" Kbase (Tvar "x"))] @?= [Karr Kbase Kbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "f" (Kbase `Karr` Kbase) (Tabs "x" Kbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Kbase `Karr` Kbase) `Karr` (Kbase `Karr` Kbase)]
  , testCase "|- * : unit" $ rights [typeof M.empty (SimplyExtTerm $ Tunit)] @?= [Kunit]
  , testCase "|- let x=2 in succ x : nat" $ rights [typeof M.empty (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [Knat]
  , testCase "|- {pred 1, if true then false else false} : (nat,bool)" $ rights [typeof M.empty (SimplyExtTerm $ Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse))] @?= [Kpair Knat Kbool]
  , testCase "|- (λx:(nat,bool). x.2) {pred 1, if true then false else false} : bool" $ rights [typeof M.empty (SimplyExtTerm $ (Tabs "x" (Kpair Knat Kbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [Kbool]
  , testCase "|- {1,2,true} : (nat,nat,bool)" $ rights [typeof M.empty (SimplyExtTerm $ Ttuple [Tsucc Tzero, Tsucc (Tsucc Tzero), Ttrue])] @?= [Ktuple [Knat, Knat, Kbool]]
  ]

test_eval =
  [ testCase "(λf:unit -> unit. f *) (λx:unit. x) -> *" $ rights [eval M.empty (SimplyExtTerm $ Tabs "f" (Tunit `Karr` Tunit) (Tvar "f" `Tapp` Tunit) `Tapp` (Tabs "x" Tunit (Tvar "x")))] @?= [SimplyExtTerm Tunit]
  , testCase "let x=2 in succ x -> 3" $ rights [eval M.empty (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [SimplyExtTerm (Tsucc (Tsucc (Tsucc Tzero)))]
  , testCase "{pred 1, if true then false else false}.1 -> 0" $ rights [eval M.empty (SimplyExtTerm $ Tpr1 (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tzero] 
  , testCase "(λx:(nat,bool). x.2) {pred 1, if true then false else false} -> false" $ rights [eval M.empty (SimplyExtTerm $ (Tabs "x" (Kpair Knat Kbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tfalse]
 ]


