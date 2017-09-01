module Typed.SimplyExt where

import qualified Data.Tree as T
import Typed.Simply
import Util

pattern Tbase = T.Node "A" []

pattern Tunit = T.Node "Unit" []
pattern Tstar = T.Node "*" []

pattern (:.) tx ty = (Tabs "_" Tunit ty) `Tapp` tx



