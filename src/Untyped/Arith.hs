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

instance Calculus "arith" StrTree StrTree () where
  data Term "arith" StrTree = ArithTerm StrTree deriving (Eq, Show)
  
  isValue (ArithTerm t) = go t
    where
      go :: StrTree -> Bool
      go Ttrue = True
      go Tfalse = True
      go t
        | isNat t = True
        | otherwise = False

  eval1 () (ArithTerm t) = fmap ArithTerm $ go t
    where
      go (Tif Ttrue t1 t2) = return t1
      go (Tif Tfalse t1 t2) = return t2
      go (Tif t1 t2 t3) = do
        t1' <- go t1
        return $ Tif t1' t2 t3
      go (Tsucc t) = do
        t' <- go t
        return $ Tsucc t'
      go (Tpred Tzero) = return Tzero
      go (Tpred (Tsucc n)) | isNat n = return n
      go (Tpred t) = do
        t' <- go t
        return $ Tpred t'
      go (Tiszero Tzero) = return Ttrue
      go (Tiszero (Tsucc n)) | isNat n = return Tfalse
      go (Tiszero t) = do
        t' <- go t
        return $ Tiszero t'
      go _ = throwM NoRuleApplies

