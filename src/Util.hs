{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Util where

import qualified Data.Tree as T

type ADT = T.Tree String

class Calculus c where
  type Term c
  type Value c
  type Typ c
  type Context c

  eval1 :: Term c -> m (Typ c)

  typeof1 :: Term c -> m (Typ c)

  typeof :: Term c -> m (Typ c)
  typeof = _


