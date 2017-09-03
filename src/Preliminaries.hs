{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Preliminaries where

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Functor.Foldable
import Data.Functor.Classes
import GHC.TypeLits

class Calculus (c :: Symbol) where
  type Term c
  type Type c
  type Context c

  isValue :: Term c -> Bool
  eval :: MonadCatch m => Context c -> Term c -> m (Term c)
  typeof :: MonadThrow m => Context c -> Term c -> m (Type c)

data TreeF a r = NodeF a [r] deriving (Functor, Eq, Show)
type StrTreeF = TreeF String
type Tree a = Fix (TreeF a)
type StrTree = Tree String

instance Show1 (TreeF String) where
  liftShowsPrec sp sl d (NodeF a rs) = showParen (d > 10) $
    showString "NodeF" . showChar ' ' . showString a . showChar ' ' . foldl (\sws a -> sws . sp 11 a) id rs

instance Eq1 (TreeF String) where
  liftEq f (NodeF a r) (NodeF b r') = a == b && length r == length r' && all (uncurry f) (zip r r')

pattern Node a r = Fix (NodeF a r)

data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

