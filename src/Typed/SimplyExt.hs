module Typed.SimplyExt
  ( module Typed.Simply
  , pattern Tbase
  , pattern Tunit
  , pattern Tstar
  , pattern (:.)
  , pattern Tas
  , pattern Tlet
  , Term(SimplyExtTerm)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import Preliminaries
import Typed.Simply

pattern Tbase = Node "A" []

pattern Tunit = Node "unit" []
pattern Tstar = Node "*" []
pattern (:.) tx ty = (Tabs "*" Tunit ty) `Tapp` tx

pattern Tas t typ = Node "as" [t,typ]

pattern Tlet x t1 t2 = Node "let _ = _ in _" [Tval x,t1,t2]

data TypeOfError
  = ExpectedType StrTree
  deriving Show

instance Exception TypeOfError

instance Calculus "simply-ext" StrTree StrTree (M.Map Var Binding) where
  newtype Term "simply-ext" StrTree = SimplyExtTerm StrTree deriving (Eq, Show)

  isValueR rec' (SimplyExtTerm t) = go t where
    go Tstar = True
    go t = isValue (SimplyTerm t)

  typeofR rec' ctx (SimplyExtTerm t) = go ctx t where
    rec ctx = rec' ctx . SimplyExtTerm

    go ctx Tstar = return Tunit
    go ctx (Tas t typ) = do
      tt <- rec ctx t
      if tt == typ
        then return typ
        else throwM $ ExpectedType typ
    go ctx (Tlet x t1 t2) = do
      t1T <- rec ctx t1
      t2T <- rec (M.insert x (VarBind t1T) ctx) t2
      return t2T
    go ctx t = typeofR (\ctx' (SimplyTerm t) -> rec' ctx' (SimplyExtTerm t)) ctx (SimplyTerm t)

  evalR rec' ctx (SimplyExtTerm t) = fmap SimplyExtTerm $ go ctx t where
    rec ctx = fmap (\(SimplyExtTerm t) -> t) . rec' ctx . SimplyExtTerm

    go ctx (Tas v typ)
      | isValue (SimplyExtTerm v) = return v
      | otherwise = fmap (\t -> Tas t typ) $ rec ctx v
    go ctx (Tlet x v t)
      | isValue (SimplyExtTerm v) = return $ subst x v t
      | otherwise = do
        v' <- rec ctx v
        return $ Tlet x v t
    go ctx t = fmap (\(SimplyTerm t) -> t) $ evalR (\ctx' (SimplyTerm t) -> fmap (\(SimplyExtTerm t) -> SimplyTerm t) $ rec' ctx' (SimplyExtTerm t)) ctx (SimplyTerm t)

    subst :: Var -> StrTree -> StrTree -> StrTree
    subst x v = go where
      go (Tsucc t) = Tsucc (go t)
      go (Tpred t) = Tpred (go t)
      go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
      go (Tvar y)
        | x == y = v
        | otherwise = Tvar y
      go (Tabs y yt t)
        | x == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)
      go t = t


