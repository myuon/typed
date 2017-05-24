{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Recursive where

import Control.Monad.Catch
import Data.Tagged
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Simply

--

class SpType typ => RecType typ where
  tvar :: String -> typ
  mu :: String -> typ -> typ

  substTVar :: String -> typ -> typ -> typ

pattern Ptvar t = T.Node t []
pattern Pmu s t = T.Node s [t]

instance RecType Syntax where
  tvar = Ptvar
  mu = Pmu

  substTVar v ty (Parrow s1 s2) = Parrow (substTVar v ty s1) (substTVar v ty s2)
  substTVar v ty (Ptvar w)
    | v == w = ty
    | otherwise = Ptvar w
  substTVar v ty (Pmu a ty') = Pmu a ty'

--

class SpExp var typ repr => RecExp var typ repr where
  fold :: typ -> repr -> repr
  unfold :: typ -> repr -> repr

pattern Pfold t s = T.Node "fold" [t,s]
pattern Punfold t s = T.Node "unfold" [t,s]

instance RecExp Int Syntax Syntax where
  fold = Pfold
  unfold = Punfold

-- 

instance MonadThrow m => RecExp Int Syntax (ContextOf m) where
  fold ty exp = Tagged go where
    go ctx =
      case ty of
        Pmu x t1 -> seq (typecheck @"context" ctx exp (substTVar x ty t1)) $ return ty
        z -> throwM' $ show ty `should` (show $ Pmu "" wild)
  unfold ty exp = Tagged go where
    go ctx =
      case ty of
        Pmu x t1 -> seq (typecheck @"context" ctx exp ty) $ return $ substTVar x ty t1
        z -> throwM' $ show ty `should` (show $ Pmu "" wild)
  
