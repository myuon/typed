{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
module Preliminaries where

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Functor.Foldable
import Data.Functor.Classes
import Data.Proxy
import GHC.TypeLits

class Calculus (c :: Symbol) trm typ ctx | c -> trm typ ctx where
  isValue :: trm -> Bool
  typeof :: MonadThrow m => ctx -> trm -> m typ
  eval1 :: MonadThrow m => ctx -> trm -> m trm

eval :: (Calculus c trm typ ctx, MonadCatch m) => proxy c -> ctx -> trm -> m trm
eval p ctx t = catch (eval1 ctx t) $ \case
  NoRuleApplies -> return t

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

