module Untyped.Untyped where

import Control.Monad.Catch
import qualified Data.Map as M
import Preliminaries

pattern Tnat x = Node x []
pattern Tvar x = Node "var" [Tnat x]
pattern Tabs t = Node "lambda" [t]
pattern Tapp tx ty = Node "app" [tx,ty]

data Binding = NameBind
type Var = String

evalUntyped :: MonadThrow m => M.Map Var Binding -> StrTree -> m StrTree
evalUntyped ctx = go where
  go (Tapp (Tabs t) v) | isValue @"untyped" v = return $ substTop v t
  go (Tapp v t) | isValue @"untyped" v = do
    t' <- evalUntyped ctx t
    return $ Tapp v t'
  go (Tapp tx ty) = do
    tx' <- evalUntyped ctx tx
    return $ Tapp tx' ty
  go _ = throwM NoRuleApplies

  shift :: Int -> StrTree -> StrTree
  shift d = go 0
    where
      go c (Tvar x)
        | read x >= c = Tvar (show $ read x + d)
        | otherwise = Tvar x
      go c (Tabs t) = Tabs (go (c+1) t)
      go c (Tapp tx ty) = Tapp (go c tx) (go c ty)

  subst :: Int -> StrTree -> StrTree -> StrTree
  subst j s = go 0 where
    go c (Tvar x)
      | read x == j + c = shift c s
      | otherwise = Tvar x
    go c (Tabs t) = Tabs (go (c+1) t)
    go c (Tapp tx ty) = Tapp (go c tx) (go c ty)

  substTop :: StrTree -> StrTree -> StrTree
  substTop s = shift (-1) . subst 0 (shift 1 s)

instance Calculus "untyped" where
  type Term "untyped" = StrTree
  type Type "untyped" = StrTree
  type Context "untyped" = M.Map Var Binding

  isValue (Tabs _) = True
  isValue _ = False

  eval ctx t = catch (evalUntyped ctx t) $ \case
    NoRuleApplies -> return t

