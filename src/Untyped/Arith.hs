{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module Untyped.Arith where

import Control.Monad.Catch
import Preliminaries

pattern Ttrue = NodeF "true" []
pattern Tfalse = NodeF "false" []
pattern Tif b t1 t2 = NodeF "if_then_else" [b, t1, t2]
pattern Tzero = NodeF "0" []
pattern Tsucc n = NodeF "succ" [n]
pattern Tpred n = NodeF "pred" [n]
pattern Tiszero n = NodeF "iszero" [n]

instance TreeCalculus (Wrapped "arith" StrTree) where
  isValue1 Ttrue = True
  isValue1 Tfalse = True
  isValue1 t
    | isNat t = True
    | otherwise = False

    where
      isNat :: TreeF String Bool -> Bool
      isNat Tzero = True
      isNat (Tsucc t) = t
      isNat _ = False

  eval1 = go where
    go :: StrTreeF (m StrTree) -> m StrTree
    go (Tif Ttrue t1 t2) = t1
{-

data ArithEvalException = NoRuleApplies deriving Show
instance Exception ArithEvalException

eval1 :: MonadThrow m => ADT -> m ADT
eval1 (Tif Ttrue t1 t2) = return t1
eval1 (Tif Tfalse t1 t2) = return t2
eval1 (Tif t1 t2 t3) = do
  t1' <- eval1 t1
  return $ Tif t1' t2 t3
eval1 (Tsucc t) = do
  t' <- eval1 t
  return $ Tsucc t'
eval1 (Tpred Tzero) = return Tzero
eval1 (Tpred (Tsucc n)) | isNat n = return n
eval1 (Tpred t) = do
  t' <- eval1 t
  return $ Tpred t'
eval1 (Tiszero Tzero) = return Ttrue
eval1 (Tiszero (Tsucc n)) | isNat n = return Tfalse
eval1 (Tiszero t) = do
  t' <- eval1 t
  return $ Tiszero t'
eval1 _ = throwM NoRuleApplies

eval :: MonadCatch m => ADT -> m ADT
eval t = catch (eval1 t) $ \case
  NoRuleApplies -> return t
-}

