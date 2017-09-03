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

instance Calculus "simply" where
  type Term "simply" = StrTree
  type Type "simply" = StrTree
  type Context "simply" = M.Map Var Binding

  isValue (Tabs _ _ _) = True
  isValue Ttrue = True
  isValue Tfalse = True
  isValue _ = False

  typeof = go where
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

  eval ctx t = catch (eval1 ctx t) $ \case
    NoRuleApplies -> return t

    where
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

      eval1 :: MonadThrow m => Context "simply" -> StrTree -> m StrTree
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
          | isValue @"simply" tx = do
            ty' <- eval1 ctx ty
            return $ Tapp tx ty'
          | otherwise = do
            tx' <- eval1 ctx tx
            return $ Tapp tx' ty
        go t = return t

