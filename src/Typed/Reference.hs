module Typed.Reference
  ( module M
  , pattern Tref
  , pattern Tderef
  , pattern Tassign
  , pattern Tloc
  , pattern Kref
  , Term(ReferenceTerm)
  , EvalTerm(RefEvalTerm)
  ) where

import Control.Monad
import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Data.Unique
import Preliminaries
import Typed.Simply as M (pattern Tval, pattern Tvar, pattern Tabs, pattern Tapp, pattern Karr)
import Typed.SimplyExt as M (pattern Tunit, pattern Kunit)

pattern Tref t = T.Node "ref {}" [t]
pattern Tderef t = T.Node "!{}" [t]
pattern Tassign t1 t2 = T.Node "{} := {}" [t1,t2]
pattern Tloc l = Tval l
pattern Kref t = T.Node "Ref {}" [t]

type Loc = String

data TypeOfError
  = ExpectedType StrTree StrTree
  deriving Show

instance Exception TypeOfError

instance Calculus "reference" StrTree StrTree (M.Map Var StrTree, M.Map Loc StrTree) where
  data Term "reference" StrTree = ReferenceTerm StrTree deriving (Eq, Show)

  isValue (ReferenceTerm t) = go t where
    go (Tabs _ _ _) = True
    go Tunit = True
    go (Tloc _) = True
    go _ = False

  typeof arg (ReferenceTerm t) = go arg t where
    go (ctx,sto) (Tvar x) = return $ ctx M.! x
    go (ctx,sto) (Tabs x xt t) = do
      tT <- go (M.insert x xt ctx,sto) t
      return $ xt `Karr` tT
    go (ctx,sto) (Tapp t1 t2) = do
      go (ctx,sto) t1 >>= \case
        Karr t1T1 t1T2 -> do
          _ <- join $ liftM2 (expect ExpectedType) (return t1T1) (go (ctx,sto) t2)
          return $ t1T2
        z -> throwM $ ExpectedType (Karr (Tval "_") (Tval "_")) z
    go (ctx,sto) Tunit = return Kunit
    go (ctx,sto) (Tloc l) = return $ Kref $ sto M.! l
    go (ctx,sto) (Tref t) = Kref <$> go (ctx,sto) t
    go (ctx,sto) (Tderef t) = do
      go (ctx,sto) t >>= \case
        Kref tT -> return tT
        z -> throwM $ ExpectedType (Kref (Tval "_")) z
    go (ctx,sto) (Tassign t1 t2) = do
      go (ctx,sto) t1 >>= \case
        Kref t1T -> do
          _ <- join $ liftM2 (expect ExpectedType) (return t1T) (go (ctx,sto) t2)
          return Kunit
        z -> throwM $ ExpectedType (Kref (Tval "_")) z

instance EvCalculus "reference" StrTree StrTree (M.Map Var StrTree, M.Map Loc StrTree) where
  data EvalTerm "reference" StrTree = RefEvalTerm StrTree (M.Map Loc StrTree) deriving (Eq, Show)

  eval1ext = go where
    go (RefEvalTerm (Tapp (Tabs x xt t1) t2) mu) | isValue (ReferenceTerm t2) = return $ RefEvalTerm (subst x t2 t1) mu
    go (RefEvalTerm (Tapp t1 t2) mu) | isValue (ReferenceTerm t1) = do
      RefEvalTerm t2' mu' <- go (RefEvalTerm t2 mu)
      return $ RefEvalTerm (Tapp t1 t2') mu'
    go (RefEvalTerm (Tapp t1 t2) mu) = do
      RefEvalTerm t1' mu' <- go (RefEvalTerm t1 mu)
      return $ RefEvalTerm (Tapp t1' t2) mu'
    go (RefEvalTerm (Tref v) mu) | isValue (ReferenceTerm v) = do
      let loc =(++ "'") $ last $ M.keys mu
      return $ RefEvalTerm (Tloc loc) (M.insert loc v mu)
    go (RefEvalTerm (Tref t) mu) = do
      RefEvalTerm t' mu' <- go (RefEvalTerm t mu)
      return $ RefEvalTerm (Tref t') mu
    go (RefEvalTerm (Tderef (Tloc l)) mu) = return $ RefEvalTerm (mu M.! l) mu
    go (RefEvalTerm (Tderef t) mu) = do
      RefEvalTerm t' mu' <- go (RefEvalTerm t mu)
      return $ RefEvalTerm (Tderef t') mu'
    go (RefEvalTerm (Tassign (Tloc l) v) mu) | isValue (ReferenceTerm v) =
      return $ RefEvalTerm Tunit (M.insert l v mu)
    go (RefEvalTerm (Tassign t1 t2) mu) | isValue (ReferenceTerm t1) = do
      RefEvalTerm t2' mu' <- go (RefEvalTerm t2 mu)
      return $ RefEvalTerm (Tassign t1 t2') mu
    go (RefEvalTerm (Tassign t1 t2) mu) = do
      RefEvalTerm t1' mu' <- go (RefEvalTerm t1 mu)
      return $ RefEvalTerm (Tassign t1' t2) mu
    go _ = throwM NoRuleApplies

    subst v p = go where
      go (Tvar y)
        | v == y = p
        | otherwise = Tvar y
      go (Tabs y yt t)
        | v == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)
      go Tunit = Tunit
      go (Tref t) = Tref (go t)
      go (Tderef t) = Tderef (go t)
      go (Tassign t1 t2) = Tassign (go t1) (go t2)

