{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module Untyped.Arith where

import Control.Monad.Catch
import Data.Functor.Foldable
import Preliminaries

pattern Ttrue = Node "true" []
pattern Tfalse = Node "false" []
pattern Tif b t1 t2 = Node "if_then_else" [b, t1, t2]
pattern Tzero = Node "0" []
pattern Tsucc n = Node "succ" [n]
pattern Tpred n = Node "pred" [n]
pattern Tiszero n = Node "iszero" [n]

data ArithEvalException = NoRuleApplies deriving Show
instance Exception ArithEvalException

isNat :: StrTree -> Bool
isNat Tzero = True
isNat (Tsucc t) = isNat t
isNat _ = False

instance Calculus (Wrapped "arith" StrTree) where
  type Term (Wrapped "arith" StrTree) = StrTree
  type Type (Wrapped "arith" StrTree) = StrTree
  type Context (Wrapped "arith" StrTree) = ()
  
  isValue = go
    where
      go :: StrTree -> Bool
      go Ttrue = True
      go Tfalse = True
      go t
        | isNat t = True
        | otherwise = False

  eval () t = catch (eval1 t) $ \case
    NoRuleApplies -> return t
    where
      eval1 :: MonadThrow m => StrTree -> m StrTree
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



