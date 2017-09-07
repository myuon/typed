{-# LANGUAGE FunctionalDependencies #-}
module Preliminaries where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import GHC.TypeLits

type Var = String

class Calculus (c :: Symbol) trm typ evctx tyctx | c -> trm typ evctx tyctx where
  data Term c trm
  isValue :: (Calculus c trm typ evctx tyctx) => Term c trm -> Bool
  eval1 :: (Calculus c trm typ evctx tyctx, MonadCatch m) => evctx -> Term c trm -> m (Term c trm)
  typeof :: (Calculus c trm typ evctx tyctx, MonadThrow m) => tyctx -> Term c trm -> m typ

eval :: (Calculus c trm typ evctx tyctx, MonadCatch m) => evctx -> Term c trm -> m (Term c trm)
eval ctx t = catch (eval1 ctx t >>= eval ctx) $ \case
  NoRuleApplies -> return t

type StrTree = T.Tree String

data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

