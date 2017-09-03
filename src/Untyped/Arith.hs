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

isNat :: StrTree -> Bool
isNat Tzero = True
isNat (Tsucc t) = isNat t
isNat _ = False

evalArith :: MonadThrow m => StrTree -> m StrTree
evalArith (Tif Ttrue t1 t2) = return t1
evalArith (Tif Tfalse t1 t2) = return t2
evalArith (Tif t1 t2 t3) = do
  t1' <- evalArith t1
  return $ Tif t1' t2 t3
evalArith (Tsucc t) = do
  t' <- evalArith t
  return $ Tsucc t'
evalArith (Tpred Tzero) = return Tzero
evalArith (Tpred (Tsucc n)) | isNat n = return n
evalArith (Tpred t) = do
  t' <- evalArith t
  return $ Tpred t'
evalArith (Tiszero Tzero) = return Ttrue
evalArith (Tiszero (Tsucc n)) | isNat n = return Tfalse
evalArith (Tiszero t) = do
  t' <- evalArith t
  return $ Tiszero t'
evalArith _ = throwM NoRuleApplies

instance Calculus "arith" StrTree StrTree () where
  isValue _ = go
    where
      go :: StrTree -> Bool
      go Ttrue = True
      go Tfalse = True
      go t
        | isNat t = True
        | otherwise = False

  eval1 p () t = evalArith t

