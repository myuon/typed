module Typed.SimplyExt where

import Control.Monad.Catch
import qualified Data.Map as M
import Preliminaries
import Untyped.Arith
import Typed.Simply

pattern Tbase = Node "A" []
pattern Tunit = Node "unit" []

pattern Tstar = Node "*" []
pattern (:.) tx ty = (Tabs "*" Tunit ty) `Tapp` tx
pattern Tas t typ = Node "as" [t,typ]

instance Calculus "simply-ext" StrTree StrTree (M.Map Var Binding) where
  newtype Term "simply-ext" StrTree = SimplyExtTerm StrTree

  isValueR rec' (SimplyExtTerm t) = go t where
    go Tstar = True
    go t = isValue (SimplyTerm t)

{-
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
  go t = t



-}
