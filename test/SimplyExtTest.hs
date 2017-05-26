{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module SimplyExtTest where

import Test.Tasty
import Test.Tasty.HUnit
import GHC.TypeLits
import qualified Data.Map as M
import Init
import AExp
import Simply
import SimplyExt

typeofTests = testGroup "typeof"
  [ testCase "|- λ0:A. 0 : A -> A" $
    typeof' @"context" (sabs 0 baseA (svar 0)) @?= Just (baseA `arrow` baseA)
  , testCase "|- λ0:(A -> A). λ1:A. 0 1 : (A -> A) -> A -> A" $
    typeof' @"context" (sabs 0 (baseA `arrow` baseA) (sabs 1 baseA (svar 0 `sapp` svar 1))) @?= Just ((baseA `arrow` baseA) `arrow` (baseA `arrow` baseA))
  , testCase "|- * : unit" $
    typeof' @"context" star @?= Just unit
  , testCase "|- λ(0:A -> unit). λ(1:A). 0 1 ## 0 : (A -> unit) -> A -> A -> unit" $
    typeof' @"context" (sabs 0 (baseA `arrow` unit) (sabs 1 baseA ((svar 0 `sapp` svar 1) ## svar 0))) @?= Just ((baseA `arrow` unit) `arrow` (baseA `arrow` (baseA `arrow` unit)))
  , testCase "|- * as unit : unit" $
    typeof' @"context" (star `typeAs` unit) @?= Just unit
  , testCase "|- λ(1:A). let 0 = λ(2:A). 2 in 0 1 : A -> A" $
    typeof' @"context" (sabs 1 baseA (letin 0 (sabs 2 baseA (svar 2)) (svar 0 `sapp` svar 1))) @?= Just (baseA `arrow` baseA)
  , testCase "|- pair 0 true : tuple nat bool" $
    typeof' @"context" (pair azero atrue) @?= Just (tuple nat bool)
  , testCase "|- fst (pair 0 true) : nat" $
    typeof' @"context" (_1 (pair azero atrue)) @?= Just nat
  , testCase "|- snd (pair 0 true) : bool" $
    typeof' @"context" (_2 (pair azero atrue)) @?= Just bool
  , testCase "|- {x = 0, y = true} : {x: nat, y: bool}" $
    typeof' @"context" (fields [("x", azero), ("y", atrue)]) @?= Just (record [("x", nat), ("y", bool)])
  , testCase "|- {x = 0, y = true}.x : nat" $
    typeof' @"context" (proj_label "x" $ fields [("x", azero), ("y", atrue)]) @?= Just nat
  , testCase "|- {x = 0, y = true}.y : bool" $
    typeof' @"context" (proj_label "y" $ fields [("x", azero), ("y", atrue)]) @?= Just bool
  , testCase "|- inL 1 as nat + bool : nat + bool" $
    typeof' @"context" (inL_as (asucc azero) (nat `coprod` bool)) @?= Just (nat `coprod` bool)
--  , testCase "|- fix(λ(0:nat). succ 0) : nat" $
--    typeof' @"context" (fixpoint $ sabs 0 nat (asucc (svar 0))) @?= Just nat
  , testCase "|- cons[nat] 1 (cons[nat] 2 (cons[nat] 3 nil[nat])) : list nat" $
    typeof' @"context" (cons_as nat (asucc azero) $ cons_as nat (asucc (asucc azero)) $ cons_as nat (asucc (asucc (asucc azero))) $ nil_as nat) @?= Just (list nat)
  ]

typeofFailTests = testGroup "typeof fail"
  [ testCase "|/- λ(0: A -> A). 0 0" $
    typeof' @"context" (sabs 0 (baseA `arrow` baseA) $ svar 0 `sapp` svar 0) @?= Nothing
  , testCase "|/- fst true" $
    typeof' @"context" (_1 atrue) @?= Nothing
  , testCase "|/- 0.x" $
    typeof' @"context" (proj_label "x" azero) @?= Nothing
  , testCase "|/- {x = 0}.y" $
    typeof' @"context" (proj_label "y" $ fields [("x", azero)]) @?= Nothing
  , testCase "|/- inL 0 as bool + bool" $
    typeof' @"context" (inL_as azero (bool `coprod` bool)) @?= Nothing
  , testCase "|/- inL 0 as bool + bool" $
    typeof' @"context" (inL_as azero (bool `coprod` bool)) @?= Nothing
  , testCase "|/- inL 0 as nat" $
    typeof' @"context" (inL_as azero nat) @?= Nothing
  , testCase "|/- tail[nat] 0" $
    typeof' @"context" (tail_as nat azero) @?= Nothing
  , testCase "|/- case <x = 0> as <x:nat> of y -> true" $
    typeof' @"context" (case_variant (tagging "x" azero (variant [("x", nat)])) [("y", 0, atrue)]) @?= Nothing
  ]

enumerationTest = testGroup "enumeration"
  [ let weekday =
           variant [ ("monday", unit)
                   , ("tuesday", unit)
                   , ("wednesday", unit)
                   , ("thursday", unit)
                   , ("friday", unit)
                   ] in
    testCase "nextBusinessDay" $
    typeof' @"context"
    (sabs 0 weekday $ case_variant (svar 0)
      [ ("monday", 1, tagging "tuesday" star weekday)
      , ("tuesday", 1, tagging "wednesday" star weekday)
      , ("wednesday", 1, tagging "thursday" star weekday)
      , ("thursday", 1, tagging "friday" star weekday)
      , ("friday", 1, tagging "monday" star weekday)
      ]
    ) @?= Just (weekday `arrow` weekday)
  ]

evalTests = testGroup "eval"
  [ testCase "0 as nat ~> 0" $
    cbv (typeAs azero nat) @?= azero
  , testCase "let x = (λy:nat. succ y) 0 in asucc x ~> 2" $
    cbv (letin 0 (sabs 1 nat (asucc (svar 1)) `sapp` azero) (asucc $ svar 0)) @?= asucc (asucc azero)
  , testCase "fst (pair 0 true) ~> 0" $
    cbv (_1 (pair azero atrue)) @?= azero
  , testCase "fst (pred 0, if true then false else false) ~> 0" $
    cbv (_1 (pair (apred azero) (aif atrue afalse afalse))) @?= azero
  , testCase "case (inL star as Unit + Unit) of inL => 0 | inR => true ~> 0" $
    cbv (case_coprod (inL_as star (coprod unit unit)) 0 azero 1 atrue) @?= azero
{-
  , testCase "letrec iseven x = ... in iseven 0 ~> true" $
    cbv (fixpoint
         (sabs 0 (nat `arrow` bool) $ sabs 1 nat $
          aif (aisZero (svar 1)) atrue $
           aif (aisZero (apred (svar 1))) afalse $
           svar 0 `sapp` apred (apred (svar 1)))
         azero) @?= atrue
-}
  ]

mainTests =
  [ typeofTests
  , typeofFailTests
  , enumerationTest
  , evalTests
  ]
