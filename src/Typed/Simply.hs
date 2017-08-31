module Typed.Simply where

import Control.Monad.Catch
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
pattern Tvar x n = T.Node "var" [Tnat x,Tnat n]
pattern Tabs x xt t = T.Node "lambda" [Tnat x,xt,t]
pattern Tapp tx ty = T.Node "app" [tx,ty]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | WrongKindOfBindingForVariable
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
  go (Tvar x _) = case ctx M.! x of
    NameBind -> throwM WrongKindOfBindingForVariable
    VarBind typ -> return typ
  go (Tabs x xt t) = do
    let ctx' = M.insert x (VarBind xt) ctx
    tt <- typeof ctx' t
    return $ Tarr xt tt


