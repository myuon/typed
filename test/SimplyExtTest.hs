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
    typeof M.empty (sabs 0 baseA (svar 0)) @?= Just (baseA `arrow` baseA)
  , testCase "|- λ0:(A -> A). λ1:A. 0 1 : (A -> A) -> A -> A" $
    typeof M.empty (sabs 0 (baseA `arrow` baseA) (sabs 1 baseA (svar 0 `sapp` svar 1))) @?= Just ((baseA `arrow` baseA) `arrow` (baseA `arrow` baseA))
  , testCase "|- * : unit" $
    typeof M.empty star @?= Just unit
  , testCase "|- λ(0:A -> unit). λ(1:A). 0 1 ## 0 : (A -> unit) -> A -> A -> unit" $
    typeof M.empty (sabs 0 (baseA `arrow` unit) (sabs 1 baseA ((svar 0 `sapp` svar 1) ## svar 0))) @?= Just ((baseA `arrow` unit) `arrow` (baseA `arrow` (baseA `arrow` unit)))
  , testCase "|- * as unit : unit" $
    typeof M.empty (star `typeAs` unit) @?= Just unit
  , testCase "|- λ(1:A). let 0 = λ(2:A). 2 in 0 1 : A -> A" $
    typeof M.empty (sabs 1 baseA (letin 0 (sabs 2 baseA (svar 2)) (svar 0 `sapp` svar 1))) @?= Just (baseA `arrow` baseA)
  , testCase "|- pair 0 true : tuple nat bool" $
    typeof M.empty (pair azero atrue) @?= Just (tuple nat bool)
  , testCase "|- fst (pair 0 true) : nat" $
    typeof M.empty (_1 (pair azero atrue)) @?= Just nat
  , testCase "|- snd (pair 0 true) : bool" $
    typeof M.empty (_2 (pair azero atrue)) @?= Just bool
  , testCase "|- {x = 0, y = true} : {x: nat, y: bool}" $
    typeof M.empty (fields [("x", azero), ("y", atrue)]) @?= Just (record [("x", nat), ("y", bool)])
  , testCase "|- {x = 0, y = true}.x : nat" $
    typeof M.empty (proj_label "x" $ fields [("x", azero), ("y", atrue)]) @?= Just nat
  , testCase "|- {x = 0, y = true}.y : bool" $
    typeof M.empty (proj_label "y" $ fields [("x", azero), ("y", atrue)]) @?= Just bool
  , testCase "|- inL 1 as nat + bool : nat + bool" $
    typeof M.empty (inL_as (asucc azero) (nat `coprod` bool)) @?= Just (nat `coprod` bool)
  , testCase "|- fix(λ(0:nat). succ 0) : nat" $
    typeof M.empty (fixpoint $ sabs 0 nat (asucc (svar 0))) @?= Just nat
  , testCase "|- cons[nat] 1 (cons[nat] 2 (cons[nat] 3 nil[nat])) : list nat" $
    typeof M.empty (cons_as nat (asucc azero) $ cons_as nat (asucc (asucc azero)) $ cons_as nat (asucc (asucc (asucc azero))) $ nil_as nat) @?= Just (list nat)
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
    typeof M.empty
    (sabs 0 weekday $ case_variant (svar 0)
      [ ("monday", 1, tagging "tuesday" star weekday)
      , ("tuesday", 1, tagging "wednesday" star weekday)
      , ("wednesday", 1, tagging "thursday" star weekday)
      , ("thursday", 1, tagging "friday" star weekday)
      , ("friday", 1, tagging "monday" star weekday)
      ]
    ) @?= Just (weekday `arrow` weekday)
  ]

simplyExtTests =
  [ typeofTests
  , enumerationTest
  ]
