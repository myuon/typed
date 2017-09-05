module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.SimplyExt

test_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "x" Tbase (Tvar "x"))] @?= [Tarr Tbase Tbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "f" (Tbase `Tarr` Tbase) (Tabs "x" Tbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Tbase `Tarr` Tbase) `Tarr` (Tbase `Tarr` Tbase)]
  , testCase "|- * : unit" $ rights [typeof M.empty (SimplyExtTerm $ Tstar)] @?= [Tunit]
  , testCase "|- let x=2 in succ x : nat" $ rights [typeof M.empty (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [Tnat]
  , testCase "|- {pred 1, if true then false else false} : (nat,bool)" $ rights [typeof M.empty (SimplyExtTerm $ Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse))] @?= [Tprod Tnat Tbool]
  , testCase "|- (λx:(nat,bool). x.2) {pred 1, if true then false else false} : bool" $ rights [typeof M.empty (SimplyExtTerm $ (Tabs "x" (Tprod Tnat Tbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [Tbool]
  ]

test_eval =
  [ testCase "(λf:unit -> unit. f *) (λx:unit. x) -> *" $ rights [eval M.empty (SimplyExtTerm $ Tabs "f" (Tunit `Tarr` Tunit) (Tvar "f" `Tapp` Tstar) `Tapp` (Tabs "x" Tunit (Tvar "x")))] @?= [SimplyExtTerm Tstar]
  , testCase "let x=2 in succ x -> 3" $ rights [eval M.empty (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [SimplyExtTerm (Tsucc (Tsucc (Tsucc Tzero)))]
  , testCase "{pred 1, if true then false else false}.1 -> 0" $ rights [eval M.empty (SimplyExtTerm $ Tpr1 (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tzero] 
  , testCase "(λx:(nat,bool). x.2) {pred 1, if true then false else false} -> false" $ rights [eval M.empty (SimplyExtTerm $ (Tabs "x" (Tprod Tnat Tbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tfalse]
 ]


