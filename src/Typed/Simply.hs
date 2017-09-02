{-# LANGUAGE TypeFamilies #-}
module Typed.Simply where

import Control.Monad.Catch
import Control.Monad.Fix
import qualified Data.Tree as T
import qualified Data.Map as M
import Util

type Typ = T.Tree String
type Var = String
type Context = M.Map Var Binding
data Binding = NameBind | VarBind Typ

pattern Tbool = T.Node "bool" []
pattern Tarr a b = T.Node "->" [a,b]

pattern Ttrue = T.Node "true" []
pattern Tfalse = T.Node "false" []
pattern Tif b t1 t2 = T.Node "if_then_else" [b, t1, t2]

pattern Tnat x = T.Node x []
pattern Tvar x = T.Node "var" [Tnat x]
pattern Tabs x xt t = T.Node "lambda" [Tnat x,xt,t]
pattern Tapp tx ty = T.Node "app" [tx,ty]


data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

typeof :: MonadThrow m => Context -> ADT -> m Typ
typeof ctx = go where
  go Ttrue = return Tbool
  go Tfalse = return Tbool
  go (Tif t a b) = do
    tt <- typeof ctx t
    if tt == Tbool
      then do
      ta <- typeof ctx a
      tb <- typeof ctx b
      if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
      else throwM GuardOfConditionalNotABoolean
  go (Tvar x) = case ctx M.! x of
    NameBind -> throwM WrongKindOfBindingForVariable
    VarBind typ -> return typ
  go (Tabs x xt t) = do
    let ctx' = M.insert x (VarBind xt) ctx
    tt <- typeof ctx' t
    return $ Tarr xt tt
  go (Tapp tx ty) = do
    txTyp <- typeof ctx tx
    tyTyp <- typeof ctx ty
    case txTyp of
      Tarr txTyp1 txTyp2 ->
        if tyTyp == txTyp1 then return txTyp2
        else throwM ParameterTypeMismatch
      _ -> throwM ArrowTypeExpected

data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

isVal :: ADT -> Bool
isVal (Tabs _ _ _) = True
isVal Ttrue = True
isVal Tfalse = True
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
  go t = return t

eval :: MonadCatch m => Context -> ADT -> m ADT
eval ctx t = catch (eval1 ctx t) $ \case
  NoRuleApplies -> return t

