module Untyped.Untyped where

import Control.Monad.Catch
import qualified Data.Tree as T
import qualified Data.Map as M
import Preliminaries

pattern Knat x = T.Node x []
pattern Tvar x = T.Node "var" [Knat x]
pattern Tabs t = T.Node "lambda" [t]
pattern Tapp tx ty = T.Node "app" [tx,ty]

data Binding = NameBind

instance Calculus "untyped" StrTree StrTree () () where
  data Term "untyped" StrTree = UntypedTerm StrTree deriving (Eq, Show)

  isValue (UntypedTerm t) = go t where
    go (Tabs _) = True
    go _ = False

  eval1 ctx (UntypedTerm t) = fmap UntypedTerm $ go ctx t where
    go ctx (Tapp (Tabs t) v) | isValue (UntypedTerm v) = return $ substTop v t
    go ctx (Tapp v t) | isValue (UntypedTerm v) = do
      t' <- go ctx t
      return $ Tapp v t'
    go ctx (Tapp tx ty) = do
      tx' <- go ctx tx
      return $ Tapp tx' ty
    go _ _ = throwM NoRuleApplies

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


