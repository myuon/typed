{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Untyped where

import Control.Monad
import Data.Tagged
import GHC.TypeLits
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Set as S
import Init

-- syntax tree

class UVal repr where
  uabs :: repr -> repr

class UVal repr => UExp var repr | repr -> var where
  uvar :: var -> repr
  uapp :: repr -> repr -> repr
  uisVal :: repr -> Bool

pattern V v = T.Node v []
pattern Pvar var = T.Node "var" [V var]
pattern Pabs exp = T.Node "abs" [exp]
pattern Papp exp1 exp2 = T.Node "app" [exp1,exp2]

instance UVal Syntax where
  uabs exp = Pabs exp

instance UExp Int Syntax where
  uvar = Pvar . show
  uapp = Papp

  uisVal (Pabs _) = True
  uisVal _ = False

-- call-by-value

instance UVal CBV where
  uabs t = Tagged $ Pabs $ unTagged t

instance UExp Int CBV where
  uisVal m =
    case unTagged m of
      Pabs _ -> True
      _ -> False

  uvar v = Tagged $ Pvar $ show v
  uapp m1 m2 =
    case unTagged m1 of
      Pabs m1' | uisVal m2 -> shift (-1) (subst 0 (shift 1 m2) (Tagged m1'))
      _ | uisVal m1 -> 
        let m2' = Tagged $ unTagged m2 in
        if unTagged m2 == unTagged m2' then Tagged $ Papp (unTagged m1) (unTagged m2)
        else uapp m1 m2'
      _ ->
        let m1' = Tagged $ unTagged m1 in
        if unTagged m1 == unTagged m1' then Tagged $ Papp (unTagged m1) (unTagged m2)
        else uapp m1' m2

    where
      shift :: Int -> Tagged "cbv" Syntax -> Tagged "cbv" Syntax
      shift d = go d 0 where
        go :: Int -> Int -> Tagged "cbv" Syntax -> Tagged "cbv" Syntax
        go d c (Tagged (Pvar k_)) = let k = read k_ in
          if k < c then uvar k
          else uvar (k + d)
        go d c (Tagged (Pabs exp)) = uabs (go d (c+1) (Tagged exp))
        go d c (Tagged (Papp exp1 exp2)) = uapp (go d c (Tagged exp1)) (go d c (Tagged exp2))

      subst :: Int -> Tagged "cbv" Syntax -> Tagged "cbv" Syntax -> Tagged "cbv" Syntax
      subst j s (Tagged (Pvar k_)) = let k = read k_ in
        if k == j then s else uvar k
      subst j s (Tagged (Pabs exp)) = uabs (subst (j+1) (shift 1 s) (Tagged exp))
      subst j s (Tagged (Papp exp1 exp2)) = uapp (subst j s (Tagged exp1)) (subst j s (Tagged exp2))
