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

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Functor.Foldable
import GHC.TypeLits

class Calculus c where
  type Term c
  type Type c
  type Context c

  isValue :: Term c -> Bool
  eval :: MonadCatch m => Term c -> m (Term c)
  typeof :: MonadThrow m => Context c -> Term c -> m (Type c)

data TreeF a r = NodeF a [r] deriving (Functor)
type StrTreeF = TreeF String
type Tree a = Fix (TreeF a)
type StrTree = Tree String

newtype Wrapped (symbol :: Symbol) a = Wrapped { unWrapped :: a }
type instance Base (Wrapped symbol a) = Base a

pattern Node a r = Fix (NodeF a r)

