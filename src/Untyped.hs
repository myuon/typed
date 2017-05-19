{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Untyped where

import Control.Monad
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Set as S

type Syntax = T.Tree String

-- syntax tree

class UVal repr where
  uabs :: repr -> repr

class UVal repr => UExp repr where
  type Var repr
  uvar :: Var repr -> repr
  uapp :: repr -> repr -> repr
  uisVal :: repr -> Bool

pattern V v = T.Node v []
pattern Pvar var = T.Node "var" [V var]
pattern Pabs exp = T.Node "abs" [exp]
pattern Papp exp1 exp2 = T.Node "app" [exp1,exp2]

instance UVal Syntax where
  uabs exp = Pabs exp

instance UExp Syntax where
  type Var Syntax = Int
  uvar a = V $ show a
  uapp = Papp

  uisVal (Pabs _) = True
  uisVal _ = False

-- call-by-value

class (Eq repr, UExp repr) => UEval repr where
  ueval1 :: repr -> repr

  ueval :: repr -> repr
  ueval r = let r' = ueval1 r in
    if r == r' then r
    else ueval r'

instance UEval Syntax where
  ueval1 = go where
    shift :: Int -> Syntax -> Syntax
    shift d = go d 0 where
      go :: Int -> Int -> Syntax -> Syntax
      go d c (Pvar k_) = let k = read k_ in
        if k < c then Pvar (show k)
        else Pvar (show $ k + d)
      go d c (Pabs exp) = Pabs (go d (c+1) exp)
      go d c (Papp exp1 exp2) = Papp (go d c exp1) (go d c exp2)

    subst :: Int -> Syntax -> Syntax -> Syntax
    subst j s (Pvar k_) = let k = read k_ in
      if k == j then s else Pvar (show k)
    subst j s (Pabs exp) = Pabs (subst (j+1) (shift 1 s) exp)
    subst j s (Papp exp1 exp2) = Papp (subst j s exp1) (subst j s exp2)
    
    go :: Syntax -> Syntax
    go (Papp (Pabs exp1) exp2) | uisVal exp2 = shift (-1) (subst 0 (shift 1 exp2) exp1)
    go (Papp exp1 exp2) | uisVal exp1 = Papp exp1 (go exp2)
    go (Papp exp1 exp2) = Papp (go exp1) exp2
    go e = e


