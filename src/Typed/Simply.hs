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
import Control.Monad.Fix
import qualified Data.Map as M
import Preliminaries
import Typed.Arith as M

data Binding = NameBind | VarBind StrTree

pattern Tarr a b = Node "->" [a,b]

pattern Tval x = Node x []
pattern Tvar x = Node "var" [Tval x]
pattern Tabs x xt t = Node "lambda" [Tval x,xt,t]
pattern Tapp tx ty = Node "app" [tx,ty]

data TypeOfError
  = WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

instance Calculus "simply" StrTree StrTree (M.Map Var Binding) where
  data Term "simply" StrTree = SimplyTerm StrTree deriving (Eq, Show)

  isValueR rec' (SimplyTerm t) = go t where
    go (Tabs _ _ _) = True
    go t = isValueR (rec' . (\(ArithTerm t) -> SimplyTerm t)) (ArithTerm t)

  typeofR rec' ctx (SimplyTerm t) = go ctx t where
    rec ctx = rec' ctx . SimplyTerm
    
    go ctx (Tvar x) = case ctx M.! x of
      NameBind -> throwM WrongKindOfBindingForVariable
      VarBind typ -> return typ
    go ctx (Tabs x xt t) = do
      let ctx' = M.insert x (VarBind xt) ctx
      tt <- rec ctx' t
      return $ Tarr xt tt
    go ctx (Tapp tx ty) = do
      txTyp <- rec ctx tx
      tyTyp <- rec ctx ty
      case txTyp of
        Tarr txTyp1 txTyp2 ->
          if tyTyp == txTyp1 then return txTyp2
          else throwM ParameterTypeMismatch
        _ -> throwM ArrowTypeExpected
    go ctx t = typeofR (\() (ArithTerm t) -> rec' ctx (SimplyTerm t)) () (ArithTerm t)

  substR rec' v (SimplyTerm p) (SimplyTerm t) = SimplyTerm $ go t where
    rec = (\(SimplyTerm t) -> t) . rec' v (SimplyTerm p) . SimplyTerm

    go (Tvar y)
      | v == y = p
      | otherwise = Tvar y
    go (Tabs y yt t)
      | v == y = Tabs y yt t
      | otherwise = Tabs y yt (rec t)
    go (Tapp t1 t2) = Tapp (go t1) (go t2)
    go t = (\(ArithTerm t) -> t) $ substR (\v (ArithTerm p) (ArithTerm t) -> (\(SimplyTerm t) -> ArithTerm t) $ rec' v (SimplyTerm p) (SimplyTerm t)) v (ArithTerm p) (ArithTerm t)

  evalR sbt rec' ctx (SimplyTerm t) = fmap SimplyTerm $ go ctx t where
    rec ctx = fmap (\(SimplyTerm t) -> t) . rec' ctx . SimplyTerm
    
    go ctx (Tvar x) = return $ Tvar x
    go ctx (Tabs x xt t) = return $ Tabs x xt t
    go ctx (Tapp (Tabs x typ11 t12) v) = return $ (\(SimplyTerm t) -> t) $ sbt x (SimplyTerm v) (SimplyTerm t12)
    go ctx (Tapp tx ty)
      | isValue (SimplyTerm tx) = do
        ty' <- rec ctx ty
        return $ Tapp tx ty'
      | otherwise = do
        tx' <- rec ctx tx
        return $ Tapp tx' ty
    go ctx t = fmap (\(ArithTerm t) -> t) $ evalR (\v (ArithTerm p) (ArithTerm t) -> (\(SimplyTerm t) -> ArithTerm t) $ sbt v (SimplyTerm p) (SimplyTerm t)) (\() (ArithTerm t) -> fmap ArithTerm $ rec ctx t) () (ArithTerm t)

