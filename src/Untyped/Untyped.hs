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

instance Calculus "untyped" StrTree StrTree (M.Map Var Binding) where
  isValue _ (Tabs _) = True
  isValue _ _ = False

  eval1 p ctx = go where
    go (Tapp (Tabs t) v) | isValue p v = return $ substTop v t
    go (Tapp v t) | isValue p v = do
      t' <- eval1 p ctx t
      return $ Tapp v t'
    go (Tapp tx ty) = do
      tx' <- eval1 p ctx tx
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


