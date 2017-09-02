{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Preliminaries where

import qualified Data.Map as M
import Data.Functor.Foldable
import GHC.TypeLits

class Calculus c where
  type Term c
  type Typ c
  type Context c

  isValue :: Term c -> Bool
  eval :: Term c -> m (Term c)
  typeof :: Context c -> Term c -> m (Typ c)

data TreeF a r = NodeF a [r] deriving (Functor)
type StrTreeF = TreeF String
type Tree a = Fix (TreeF a)
type StrTree = Tree String

class TreeCalculus ty where
  isValue1 :: StrTreeF Bool -> Bool
  eval1 :: StrTreeF (m ty) -> m ty
  typeof1 :: M.Map String ty -> StrTreeF (m ty) -> m ty

data Raw

instance TreeCalculus StrTree => Calculus Raw where
  type Term Raw = StrTree
  type Typ Raw = StrTree
  type Context Raw = M.Map String StrTree

  isValue = cata (isValue1 @StrTree)
  eval = cata eval1
  typeof ctx = cata (typeof1 ctx)

newtype Wrapped (symbol :: Symbol) a = Wrapped { unWrapped :: a }
type instance Base (Wrapped symbol a) = Base a

instance (TreeCalculus (Wrapped symbol StrTree), Recursive (Wrapped symbol StrTree))
  => Calculus (Wrapped symbol StrTree) where
  type Term (Wrapped symbol StrTree) = (Wrapped symbol StrTree)
  type Typ (Wrapped symbol StrTree) = (Wrapped symbol StrTree)
  type Context (Wrapped symbol StrTree) = M.Map String (Wrapped symbol StrTree)

  isValue = cata (isValue1 @(Wrapped symbol StrTree))
  eval = cata eval1
  typeof ctx = cata (typeof1 ctx)
