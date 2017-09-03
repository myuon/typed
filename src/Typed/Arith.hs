module Typed.Arith
  ( module M
  , Term(ArithTerm)
  , pattern Tbool
  , pattern Tnat
  ) where

import Control.Monad.Catch
import Untyped.Arith as M hiding (ArithTerm)
import Preliminaries

pattern Tbool = Node "bool" []
pattern Tnat = Node "nat" []

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  deriving Show
instance Exception TypeOfError

instance Calculus "typed.arith" StrTree StrTree () where
  newtype Term "typed.arith" StrTree = ArithTerm StrTree deriving (Eq, Show)

  isValueR rec' (ArithTerm t) = go t where
    go Ttrue = True
    go Tfalse = True
    go t = isNat t

  typeofR rec' ctx (ArithTerm t) = go ctx t where
    rec ctx = rec' ctx . ArithTerm
    
    go ctx Ttrue = return Tbool
    go ctx Tfalse = return Tbool
    go ctx (Tif t a b) = do
      tt <- rec ctx t
      case tt of
        Tbool -> do
          ta <- rec ctx a
          tb <- rec ctx b
          if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        _ -> throwM GuardOfConditionalNotABoolean
    go ctx Tzero = return Tnat
    go ctx (Tsucc t) = do
      tt <- rec ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat
    go ctx (Tpred t) = do
      tt <- rec ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat
    go ctx (Tiszero t) = do
      tt <- rec ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat

  evalR rec' ctx (ArithTerm t) = fmap ArithTerm $ go t where
    rec = fmap (\(ArithTerm t) -> t) . rec' () . ArithTerm

    go (Tif Ttrue t1 t2) = return t1
    go (Tif Tfalse t1 t2) = return t2
    go (Tif t1 t2 t3) = do
      t1' <- rec t1
      return $ Tif t1' t2 t3
    go (Tsucc t) = do
      t' <- rec t
      return $ Tsucc t'
    go (Tpred Tzero) = return Tzero
    go (Tpred (Tsucc n)) | isNat n = return n
    go (Tpred t) = do
      t' <- rec t
      return $ Tpred t'
    go (Tiszero Tzero) = return Ttrue
    go (Tiszero (Tsucc n)) | isNat n = return Tfalse
    go (Tiszero t) = do
      t' <- rec t
      return $ Tiszero t'
    go _ = throwM NoRuleApplies

