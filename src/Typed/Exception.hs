module Typed.Exception
  ( module M
  , pattern Terroras
  , Term (ExceptionTerm)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Preliminaries
import Typed.Simply as M (pattern Ttrue, pattern Tfalse, pattern Tif, pattern Kbool, pattern Tval, pattern Tvar, pattern Tabs, pattern Tapp, pattern Karr, Term (SimplyTerm))

pattern Terroras t = T.Node "error as {}" [t]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ParameterTypeMismatch
  | ArrowTypeExpected
  deriving Show

instance Exception TypeOfError

instance Calculus "exception" StrTree StrTree (M.Map Var StrTree) where
  data Term "exception" StrTree = ExceptionTerm StrTree deriving (Eq, Show)

  isValue (ExceptionTerm t) = isValue (SimplyTerm t)

  typeof ctx (ExceptionTerm t) = go ctx t where
    go ctx (Terroras t) = return t
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

  eval1 (ExceptionTerm t) = fmap ExceptionTerm $ go t where
    go (Tapp (Terroras typ) t) = return $ Terroras typ
    go (Tapp v (Terroras typ)) | isValue (ExceptionTerm v) = return $ Terroras typ
    go (Tif Ttrue t1 t2) = return t1
    go (Tif Tfalse t1 t2) = return t2
    go (Tif t1 t2 t3) = do
      t1' <- go t1
      return $ Tif t1' t2 t3
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
      go (Tvar y)
        | v == y = p
        | otherwise = Tvar y
      go (Tabs y yt t)
        | v == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)

