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

import qualified Data.Tree as T
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

-- based on ADT
type StrTree = T.Tree String

data TreeF a r = NodeF a [r] deriving (Functor)
type instance Base (T.Tree a) = TreeF a
type StrTreeF = TreeF String

instance Recursive (T.Tree a) where
  project (T.Node t ts) = NodeF t ts

class TreeCalculus tmf ty where
  isValue1 :: tmf Bool -> Bool
  eval1 :: tmf (m ty) -> m ty
  typeof1 :: M.Map String ty -> tmf (m ty) -> m ty

data Raw

instance TreeCalculus StrTreeF StrTree => Calculus Raw where
  type Term Raw = StrTree
  type Typ Raw = StrTree
  type Context Raw = M.Map String StrTree

  isValue = cata (isValue1 @_ @StrTree)
  eval = cata eval1
  typeof ctx = cata (typeof1 ctx)

class Iso a b where
  to :: a -> b
  from :: b -> a

newtype Wrapped (symbol :: Symbol) a = Wrapped { unWrapped :: a }
type instance Base (Wrapped symbol a) = Base a

instance (TreeCalculus StrTreeF (Wrapped symbol StrTree), Recursive (Wrapped symbol StrTree)) => Calculus (Wrapped symbol StrTree) where
  type Term (Wrapped symbol StrTree) = (Wrapped symbol StrTree)
  type Typ (Wrapped symbol StrTree) = (Wrapped symbol StrTree)
  type Context (Wrapped symbol StrTree) = M.Map String (Wrapped symbol StrTree)

  isValue = cata (isValue1 @_ @(Wrapped symbol StrTree))
  eval = cata eval1
  typeof ctx = cata (typeof1 ctx)
