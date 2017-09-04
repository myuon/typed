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

  substR rec' v (SimplyExtTerm p) (SimplyExtTerm t) = SimplyExtTerm $ go t where
    rec = (\(SimplyExtTerm t) -> t) . rec' v (SimplyExtTerm p) . SimplyExtTerm

    go Tstar = Tstar
    go (Tas t typ) = Tas (rec t) typ
    go (Tlet x t1 t2)
      | x == v = Tlet x t1 t2
      | otherwise = Tlet x (rec t1) (rec t2)
    go t = (\(SimplyTerm t) -> t) $ substR (\v (SimplyTerm p) (SimplyTerm t) -> (\(SimplyExtTerm t) -> SimplyTerm t) $ rec' v (SimplyExtTerm p) (SimplyExtTerm t)) v (SimplyTerm p) (SimplyTerm t)

  evalR sbt rec' ctx (SimplyExtTerm t) = fmap SimplyExtTerm $ go ctx t where
    rec ctx = fmap (\(SimplyExtTerm t) -> t) . rec' ctx . SimplyExtTerm

    go ctx (Tas v typ)
      | isValue (SimplyExtTerm v) = return v
      | otherwise = fmap (\t -> Tas t typ) $ rec ctx v
    go ctx (Tlet x v t)
      | isValue (SimplyExtTerm v) = return $ (\(SimplyExtTerm t) -> t) $ sbt x (SimplyExtTerm v) (SimplyExtTerm t)
      | otherwise = do
        v' <- rec ctx v
        return $ Tlet x v t
    go ctx t = fmap (\(SimplyTerm t) -> t) $ evalR (\v (SimplyTerm p) (SimplyTerm t) -> (\(SimplyExtTerm t) -> SimplyTerm t) $ sbt v (SimplyExtTerm p) (SimplyExtTerm t)) (\ctx' (SimplyTerm t) -> fmap (\(SimplyExtTerm t) -> SimplyTerm t) $ rec' ctx' (SimplyExtTerm t)) ctx (SimplyTerm t)


