{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Untyped.Untyped where

import Control.Monad.Catch
import qualified Data.Tree as T
import qualified Data.Map as M
import Preliminaries

pattern Tnat x = T.Node x []
pattern Tvar x = T.Node "var" [Tnat x]
pattern Tabs t = T.Node "lambda" [t]
pattern Tapp tx ty = T.Node "app" [tx,ty]

pattern Fvar x = NodeF "var" [Tnat x]
pattern Fabs t = NodeF "lambda" [t]
pattern Fapp tx ty = NodeF "app" [tx,ty]

data Binding = NameBind
type Var = String
type Context = M.Map Var Binding

instance TreeCalculus StrTreeF (Wrapped "untyped" StrTree) where
  isValue1 (Fabs _) = True
  isValue1 _ = False

  eval1 = _
{-
  eval1 ctx = go where
    go (Tapp (Tabs t) v) | isVal ctx v = return $ substTop v t
    go (Tapp v t) | isVal ctx v = do
      t' <- eval1 ctx t
      return $ Tapp v t'
    go (Tapp tx ty) = do
      tx' <- eval1 ctx tx
      return $ Tapp tx' ty
    go _ = throwM NoRuleApplies
-}

--  eval ctx t = catch (eval1 ctx t) $ \case
--    NoRuleApplies -> return t

{-
shift :: Int -> ADT -> ADT
shift d = go 0
  where
    go :: Int -> ADT -> ADT
    go c (Tvar x)
      | read x >= c = Tvar (show $ read x + d)
      | otherwise = Tvar x
    go c (Tabs t) = Tabs (go (c+1) t)
    go c (Tapp tx ty) = Tapp (go c tx) (go c ty)

subst :: Int -> ADT -> ADT -> ADT
subst j s = go 0 where
  go c (Tvar x)
    | read x == j + c = shift c s
    | otherwise = Tvar x
  go c (Tabs t) = Tabs (go (c+1) t)
  go c (Tapp tx ty) = Tapp (go c tx) (go c ty)

substTop :: ADT -> ADT -> ADT
substTop s = shift (-1) . subst 0 (shift 1 s)

isVal :: Context -> ADT -> Bool
isVal _ (Tabs _) = True
isVal _ _ = False

data UntypedEvalException = NoRuleApplies deriving Show
instance Exception UntypedEvalException

eval1 :: MonadThrow m => Context -> ADT -> m ADT
eval1 ctx = go where
  go (Tapp (Tabs t) v) | isVal ctx v = return $ substTop v t
  go (Tapp v t) | isVal ctx v = do
    t' <- eval1 ctx t
    return $ Tapp v t'
  go (Tapp tx ty) = do
    tx' <- eval1 ctx tx
    return $ Tapp tx' ty
  go _ = throwM NoRuleApplies

eval :: MonadCatch m => Context -> ADT -> m ADT
eval ctx t = catch (eval1 ctx t) $ \case
  NoRuleApplies -> return t

-}
  
