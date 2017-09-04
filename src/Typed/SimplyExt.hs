module Typed.SimplyExt
  ( module Typed.Simply
  , pattern Tbase
  , pattern Tunit
  , pattern Tstar
  , pattern (:.)
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

instance Calculus "simply-ext" StrTree StrTree (M.Map Var Binding) where
  newtype Term "simply-ext" StrTree = SimplyExtTerm StrTree deriving (Eq, Show)

  isValueR rec' (SimplyExtTerm t) = go t where
    go Tstar = True
    go t = isValue (SimplyTerm t)

  typeofR rec' ctx (SimplyExtTerm t) = go ctx t where
    rec ctx = rec' ctx . SimplyExtTerm

    go ctx Tstar = return Tunit
    go ctx t = typeofR (\ctx' (SimplyTerm t) -> rec' ctx' (SimplyExtTerm t)) ctx (SimplyTerm t)

  evalR rec' ctx (SimplyExtTerm t) = fmap SimplyExtTerm $ go ctx t where
    rec ctx = fmap (\(SimplyExtTerm t) -> t) . rec' ctx . SimplyExtTerm

    go ctx t = fmap (\(SimplyTerm t) -> t) $ evalR (\ctx' (SimplyTerm t) -> fmap (\(SimplyExtTerm t) -> SimplyTerm t) $ rec' ctx' (SimplyExtTerm t)) ctx (SimplyTerm t)


