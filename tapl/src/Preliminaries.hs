{-# LANGUAGE FunctionalDependencies #-}
module Preliminaries where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import GHC.TypeLits

type Var = String

class Calculus (c :: Symbol) trm typ ctx | c -> trm typ ctx where
  data Term c trm
  isValue :: (Calculus c trm typ ctx) => Term c trm -> Bool
  eval1 :: (Calculus c trm typ ctx, MonadCatch m) => Term c trm -> m (Term c trm)
  typeof :: (Calculus c trm typ ctx, MonadThrow m) => ctx -> Term c trm -> m typ

eval :: (Calculus c trm typ ctx, MonadCatch m) => Term c trm -> m (Term c trm)
eval t = catch (eval1 t >>= eval) $ \case
  NoRuleApplies -> return t

class Calculus c trm typ ctx => EvCalculus (c :: Symbol) trm typ ctx | c -> trm typ ctx where
  data EvalTerm c trm
  eval1ext :: (Calculus c trm typ ctx, MonadCatch m) => EvalTerm c trm -> m (EvalTerm c trm)

evalext :: (EvCalculus c trm typ ctx, MonadCatch m) => EvalTerm c trm -> m (EvalTerm c trm)
evalext t = catch (eval1ext t >>= evalext) $ \case
  NoRuleApplies -> return t

expect :: (MonadThrow m, Exception e, Eq a) => (a -> a -> e) -> a -> a -> m a
expect err exp act
  | exp == act = return exp
  | otherwise = throwM $ err exp act

type StrTree = T.Tree String

data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

