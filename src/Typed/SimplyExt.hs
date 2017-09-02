module Typed.SimplyExt where

import Control.Monad.Catch
import qualified Data.Tree as T
import Typed.Simply (pattern Ttrue, pattern Tfalse, pattern Tif, pattern Tvar, pattern Tabs, pattern Tapp, Var, Context)
import Util

pattern Tbase = T.Node "A" []
pattern Tunit = T.Node "unit" []

pattern Tstar = T.Node "*" []
pattern (:.) tx ty = (Tabs "_" Tunit ty) `Tapp` tx
pattern Tas t typ = T.Node "as" [t,typ]


data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

isVal :: ADT -> Bool
isVal (Tabs _ _ _) = True
isVal Ttrue = True
isVal Tfalse = True
isVal Tstar = True
isVal _ = False

subst :: Var -> ADT -> ADT -> ADT
subst x v = go where
  go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
  go (Tvar y)
    | x == y = v
    | otherwise = Tvar y
  go (Tabs y yt t)
    | x == y = Tabs y yt t
    | otherwise = Tabs y yt (go t)
  go (Tapp t1 t2) = Tapp (go t1) (go t2)
  go t = t

eval1 :: MonadThrow m => Context -> ADT -> m ADT
eval1 ctx = go where
  go Ttrue = return Ttrue
  go Tfalse = return Tfalse
  go (Tif Ttrue t1 t2) = return t1
  go (Tif Tfalse t1 t2) = return t2
  go (Tif t1 t2 t3) = do
    t1' <- eval1 ctx t1
    return $ Tif t1' t2 t3
  go (Tvar x) = return $ Tvar x
  go (Tabs x xt t) = return $ Tabs x xt t
  go (Tapp (Tabs x typ11 t12) v) = return $ subst x v t12
  go (Tapp tx ty)
    | isVal tx = do
      ty' <- eval1 ctx ty
      return $ Tapp tx ty'
    | otherwise = do
      tx' <- eval1 ctx tx
      return $ Tapp tx' ty
  go (Tas t typ)
    | isVal t = return t
    | otherwise = go t >>= \t' -> return $ Tas t' typ
  go t = throwM NoRuleApplies

eval :: MonadCatch m => Context -> ADT -> m ADT
eval ctx t = catch (eval1 ctx t) $ \case
  NoRuleApplies -> return t


