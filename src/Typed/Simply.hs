module Typed.Simply
  ( module M
  , pattern Tarr
  , pattern Tval
  , pattern Tvar
  , pattern Tabs
  , pattern Tapp
  , Term(SimplyTerm)
  , Binding(..)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Preliminaries
import Typed.Arith as M

data Binding = NameBind | VarBind StrTree

pattern Tarr a b = T.Node "->" [a,b]

pattern Tval x = T.Node x []
pattern Tvar x = T.Node "var" [Tval x]
pattern Tabs x xt t = T.Node "lambda" [Tval x,xt,t]
pattern Tapp tx ty = T.Node "app" [tx,ty]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

instance Calculus "simply" StrTree StrTree (M.Map Var Binding) where
  data Term "simply" StrTree = SimplyTerm StrTree deriving (Eq, Show)

  isValue (SimplyTerm t) = go t where
    go (Tabs _ _ _) = True
    go t = isValue (ArithTerm t)

  typeof ctx (SimplyTerm t) = go ctx t where
    go ctx Ttrue = return Tbool
    go ctx Tfalse = return Tbool
    go ctx (Tif t a b) = do
      tt <- go ctx t
      case tt of
        Tbool -> do
          ta <- go ctx a
          tb <- go ctx b
          if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        _ -> throwM GuardOfConditionalNotABoolean
    go ctx Tzero = return Tnat
    go ctx (Tsucc t) = do
      tt <- go ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat
    go ctx (Tpred t) = do
      tt <- go ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat
    go ctx (Tiszero t) = do
      tt <- go ctx t
      case tt of
        Tnat -> return Tnat
        _ -> throwM ExpectedANat
    go ctx (Tvar x) = case ctx M.! x of
      NameBind -> throwM WrongKindOfBindingForVariable
      VarBind typ -> return typ
    go ctx (Tabs x xt t) = do
      let ctx' = M.insert x (VarBind xt) ctx
      tt <- go ctx' t
      return $ Tarr xt tt
    go ctx (Tapp tx ty) = do
      txTyp <- go ctx tx
      tyTyp <- go ctx ty
      case txTyp of
        Tarr txTyp1 txTyp2 ->
          if tyTyp == txTyp1 then return txTyp2
          else throwM ParameterTypeMismatch
        _ -> throwM ArrowTypeExpected

  eval1 ctx (SimplyTerm t) = fmap SimplyTerm $ go ctx t where
    go ctx (Tif Ttrue t1 t2) = return t1
    go ctx (Tif Tfalse t1 t2) = return t2
    go ctx (Tif t1 t2 t3) = do
      t1' <- go ctx t1
      return $ Tif t1' t2 t3
    go ctx (Tsucc t) = do
      t' <- go ctx t
      return $ Tsucc t'
    go ctx (Tpred Tzero) = return Tzero
    go ctx (Tpred (Tsucc n)) | isNat n = return n
    go ctx (Tpred t) = do
      t' <- go ctx t
      return $ Tpred t'
    go ctx (Tiszero Tzero) = return Ttrue
    go ctx (Tiszero (Tsucc n)) | isNat n = return Tfalse
    go ctx (Tiszero t) = do
      t' <- go ctx t
      return $ Tiszero t'
    go ctx (Tvar x) = return $ Tvar x
    go ctx (Tabs x xt t) = return $ Tabs x xt t
    go ctx (Tapp (Tabs x typ11 t12) v) = return $ subst x v t12
    go ctx (Tapp tx ty)
      | isValue (SimplyTerm tx) = do
        ty' <- go ctx ty
        return $ Tapp tx ty'
      | otherwise = do
        tx' <- go ctx tx
        return $ Tapp tx' ty
    go ctx _ = throwM NoRuleApplies

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


