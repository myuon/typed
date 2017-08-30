module Untyped.Untyped where

import Control.Monad.Catch
import qualified Data.Tree as T

type ADT = T.Tree String

pattern Ttrue = T.Node "true" []
pattern Tfalse = T.Node "false" []
pattern Tif b t1 t2 = T.Node "if_then_else" [b, t1, t2]
pattern Tzero = T.Node "0" []
pattern Tsucc n = T.Node "succ" [n]
pattern Tpred n = T.Node "pred" [n]
pattern Tiszero n = T.Node "iszero" [n]

isNat :: ADT -> Bool
isNat Tzero = True
isNat (Tsucc t) = isNat t
isNat _ = False

isVal Ttrue = True
isVal Tfalse = True
isVal t | isNat t = True
isVal _ = False


data UntypedEvalException = NoRuleApplies deriving Show
instance Exception UntypedEvalException

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

