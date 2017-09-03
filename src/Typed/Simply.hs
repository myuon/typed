module Typed.Simply where

import Control.Monad.Catch
import Control.Monad.Fix
import qualified Data.Map as M
import Preliminaries
import Untyped.Arith

type Var = String
data Binding = NameBind | VarBind StrTree

pattern Tbool = Node "bool" []
pattern Tarr a b = Node "->" [a,b]

pattern Tnat x = Node x []
pattern Tvar x = Node "var" [Tnat x]
pattern Tabs x xt t = Node "lambda" [Tnat x,xt,t]
pattern Tapp tx ty = Node "app" [tx,ty]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

instance Calculus "simply" StrTree StrTree (M.Map Var Binding) where
  data Term "simply" StrTree = SimplyTerm StrTree deriving (Eq, Show)

  isValue (SimplyTerm t) = go t where
    go (Tabs _ _ _) = True
    go Ttrue = True
    go Tfalse = True
    go _ = False

  typeof ctx (SimplyTerm t) = go ctx t where
    go ctx Ttrue = return Tbool
    go ctx Tfalse = return Tbool
    go ctx (Tif t a b) = do
      tt <- go ctx t
      if tt == Tbool
        then do
        ta <- go ctx a
        tb <- go ctx b
        if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        else throwM GuardOfConditionalNotABoolean
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
    go ctx Ttrue = return Ttrue
    go ctx Tfalse = return Tfalse
    go ctx (Tif Ttrue t1 t2) = return t1
    go ctx (Tif Tfalse t1 t2) = return t2
    go ctx (Tif t1 t2 t3) = do
      t1' <- go ctx t1
      return $ Tif t1' t2 t3
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
    go ctx t = return t

    subst :: Var -> StrTree -> StrTree -> StrTree
    subst x v = go where
      go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
      go (Tvar y)
        | x == y = v
        | otherwise = Tvar y
      go (Tabs y yt t)
        | x == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)

