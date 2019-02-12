module Typed.Arith
  ( module M
  , Term(ArithTerm)
  , pattern Kbool
  , pattern Knat
  ) where

import Control.Monad.Catch
import qualified Data.Tree as T
import Untyped.Arith as M hiding (ArithTerm)
import Preliminaries

pattern Kbool = T.Node "bool" []
pattern Knat = T.Node "nat" []

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  deriving Show
instance Exception TypeOfError

instance Calculus "typed.arith" StrTree StrTree () where
  newtype Term "typed.arith" StrTree = ArithTerm StrTree deriving (Eq, Show)

  isValue (ArithTerm t) = go t where
    go Ttrue = True
    go Tfalse = True
    go t = isNat t

  typeof ctx (ArithTerm t) = go ctx t where
    go ctx Ttrue = return Kbool
    go ctx Tfalse = return Kbool
    go ctx (Tif t a b) = do
      tt <- go ctx t
      case tt of
        Kbool -> do
          ta <- go ctx a
          tb <- go ctx b
          if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        _ -> throwM GuardOfConditionalNotABoolean
    go ctx Tzero = return Knat
    go ctx (Tsucc t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat
    go ctx (Tpred t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat
    go ctx (Tiszero t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat

  eval1 (ArithTerm t) = fmap ArithTerm $ go t where
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

