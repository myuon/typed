module Typed.SimplyExtTest where

import Data.Either
import qualified Data.Map as M
import Test.Tasty.HUnit
import Preliminaries
import Typed.SimplyExt

_Tff = Tabs "ie" (Knat `Karr` Kbool) $ Tabs "x" Knat $
     Tif (Tiszero (Tvar "x")) Ttrue $
     Tif (Tiszero (Tpred (Tvar "x"))) Tfalse $
     (Tvar "ie") `Tapp` Tpred (Tpred (Tvar "x"))
_Tiseven = Tfix _Tff

test_typeof =
  [ testCase "|- λx:A. x : A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "x" Kbase (Tvar "x"))] @?= [Karr Kbase Kbase]
  , testCase "|- λf:A -> A. λx:A. f(f(x)) : (A -> A) -> A -> A" $ rights [typeof M.empty (SimplyExtTerm $ Tabs "f" (Kbase `Karr` Kbase) (Tabs "x" Kbase (Tvar "f" `Tapp` (Tvar "f" `Tapp` Tvar "x"))))] @?= [(Kbase `Karr` Kbase) `Karr` (Kbase `Karr` Kbase)]
  , testCase "|- * : unit" $ rights [typeof M.empty (SimplyExtTerm $ Tunit)] @?= [Kunit]
  , testCase "|- let x=2 in succ x : nat" $ rights [typeof M.empty (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [Knat]
  , testCase "|- {pred 1, if true then false else false} : (nat,bool)" $ rights [typeof M.empty (SimplyExtTerm $ Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse))] @?= [Kpair Knat Kbool]
  , testCase "|- (λx:(nat,bool). x.2) {pred 1, if true then false else false} : bool" $ rights [typeof M.empty (SimplyExtTerm $ (Tabs "x" (Kpair Knat Kbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [Kbool]
  , testCase "|- {1,2,true} : (nat,nat,bool)" $ rights [typeof M.empty (SimplyExtTerm $ Ttuple [Tsucc Tzero, Tsucc (Tsucc Tzero), Ttrue])] @?= [Ktuple [Knat, Knat, Kbool]]
  , testCase "|- {x=0, isHoge=true} : {x:nat, isHoge:bool}" $ rights [typeof M.empty (SimplyExtTerm $ Trecord [Tfield "x" Tzero, Tfield "isHoge" Ttrue])] @?= [Krecord [Kfield "x" Knat, Kfield "isHoge" Kbool]]
  , testCase "|- ff : (nat -> bool) -> nat -> bool" $ rights [typeof M.empty (SimplyExtTerm _Tff)] @?= [(Knat `Karr` Kbool) `Karr` (Knat `Karr` Kbool)]
  , testCase "|- iseven : nat -> bool" $ rights [typeof M.empty (SimplyExtTerm _Tiseven)] @?= [Knat `Karr` Kbool]
  ]

test_eval =
  [ testCase "(λf:unit -> unit. f *) (λx:unit. x) -> *" $ rights [eval (SimplyExtTerm $ Tabs "f" (Tunit `Karr` Tunit) (Tvar "f" `Tapp` Tunit) `Tapp` (Tabs "x" Tunit (Tvar "x")))] @?= [SimplyExtTerm Tunit]
  , testCase "let x=2 in succ x -> 3" $ rights [eval (SimplyExtTerm $ Tlet "x" (Tsucc (Tsucc Tzero)) (Tsucc (Tvar "x")))] @?= [SimplyExtTerm (Tsucc (Tsucc (Tsucc Tzero)))]
  , testCase "{pred 1, if true then false else false}.1 -> 0" $ rights [eval (SimplyExtTerm $ Tpr1 (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tzero] 
  , testCase "(λx:(nat,bool). x.2) {pred 1, if true then false else false} -> false" $ rights [eval (SimplyExtTerm $ (Tabs "x" (Kpair Knat Kbool) (Tpr2 (Tvar "x"))) `Tapp` (Tpair (Tpred (Tsucc Tzero)) (Tif Ttrue Tfalse Tfalse)))] @?= [SimplyExtTerm Tfalse]
  , testCase "{x=pred 1, isHoge=true}.x -> 0" $ rights [eval (SimplyExtTerm $ Tprojf "x" (Trecord [Tfield "x" (Tpred (Tsucc Tzero)), Tfield "isHoge" Ttrue]))] @?= [SimplyExtTerm $ Tzero]
  , testCase "case (inr true as nat+bool) of { inl => true; inr => false } -> false" $ rights [eval (SimplyExtTerm $ Tcase (Tinras Ttrue (Knat `Ksum` Kbool)) (Tabs "x" Knat Ttrue) (Tabs "x" Kbool Tfalse))] @?= [SimplyExtTerm Tfalse]
  , testCase "|- iseven 3 -> false" $ rights [eval (SimplyExtTerm (_Tiseven `Tapp` (Tsucc (Tsucc (Tsucc Tzero)))))] @?= [SimplyExtTerm Tfalse]
  , testCase "|- iseven 2 -> true" $ rights [eval (SimplyExtTerm (_Tiseven `Tapp` (Tsucc (Tsucc Tzero))))] @?= [SimplyExtTerm Ttrue]
  ]

test_show =
  [ testCase "{x := 0}" $ show (SimplyExtTerm $ Trecord [Tfield "x" Tzero]) @?= "{x := 0}"
  , testCase "{x := 0, y := true}.label(x)" $ show (SimplyExtTerm $ Tprojf "x" (Trecord [Tfield "x" Tzero, Tfield "y" Ttrue])) @?= "{x := 0, y := true}.label(x)"
  , testCase "let x = if true then 0 else succ 0 in var y" $ show (SimplyExtTerm $ Tlet "x" (Tif Ttrue Tzero (Tsucc Tzero)) (Tvar "y")) @?= "let x = if true then 0 else succ 0 in var y"
  ]

