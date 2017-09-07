module Typed.Simply
  ( module M
  , pattern Karr
  , pattern Tval
  , pattern Tvar
  , pattern Tabs
  , pattern Tapp
  , Term(SimplyTerm)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Preliminaries
import Typed.Arith as M

pattern Karr a b = T.Node "->" [a,b]

pattern Tval x = T.Node x []
pattern Tvar x = T.Node "var {}" [Tval x]
pattern Tabs x xt t = T.Node "λ{}:{}. {}" [Tval x,xt,t]
pattern Tapp tx ty = T.Node "({} {})" [tx,ty]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

instance Calculus "simply" StrTree StrTree (M.Map Var StrTree) where
  data Term "simply" StrTree = SimplyTerm StrTree deriving (Eq, Show)

  isValue (SimplyTerm t) = go t where
    go (Tabs _ _ _) = True
    go t = isValue (ArithTerm t)

  typeof ctx (SimplyTerm t) = go ctx t where
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
    go ctx (Tvar x) = return $ ctx M.! x
    go ctx (Tabs x xt t) = do
      tt <- go (M.insert x xt ctx) t
      return $ Karr xt tt
    go ctx (Tapp tx ty) = do
      txTyp <- go ctx tx
      tyTyp <- go ctx ty
      case txTyp of
        Karr txTyp1 txTyp2 ->
          if tyTyp == txTyp1 then return txTyp2
          else throwM ParameterTypeMismatch
        _ -> throwM ArrowTypeExpected

  eval1 (SimplyTerm t) = fmap SimplyTerm $ go t where
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
    go (Tapp (Tabs x typ11 t12) v) = return $ subst x v t12
    go (Tapp tx ty)
      | isValue (SimplyTerm tx) = do
        ty' <- go ty
        return $ Tapp tx ty'
      | otherwise = do
        tx' <- go tx
        return $ Tapp tx' ty
    go _ = throwM NoRuleApplies

    subst v p = go where
      go Ttrue = Ttrue
      go Tfalse = Tfalse
      go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
      go (Tsucc t) = Tsucc (go t)
      go (Tpred t) = Tpred (go t)
      go (Tiszero t) = Tiszero (go t)
      go (Tvar y)
        | v == y = p
        | otherwise = Tvar y
      go (Tabs y yt t)
        | v == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)


