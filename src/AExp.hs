{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module AExp where

import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Set as S
import Data.Tagged
import Control.Monad
import Control.Monad.Catch
import GHC.TypeLits
import Init

-- syntax tree

class AVal repr where
  atrue :: repr
  afalse :: repr
  azero :: repr
  asucc :: repr -> repr

class AVal repr => AExp repr where
  aif :: repr -> repr -> repr -> repr
  apred :: repr -> repr
  aisZero :: repr -> repr

pattern Ptrue = T.Node "true" []
pattern Pfalse = T.Node "false" []
pattern Pzero = T.Node "0" []
pattern Psucc exp = T.Node "succ" [exp]
pattern Pif b exp1 exp2 = T.Node "if" [b, exp1, exp2]
pattern Ppred exp = T.Node "pred" [exp]
pattern PisZero exp = T.Node "iszero" [exp]

instance AVal Syntax where
  atrue = Ptrue
  afalse = Pfalse
  azero = Pzero
  asucc = Psucc

instance AExp Syntax where
  aif = Pif
  apred = Ppred
  aisZero = PisZero

-- types

class AType typ where
  bool :: typ
  nat :: typ

  -- for error message
  wild :: typ

pattern Pbool = T.Node "bool" []
pattern Pnat = T.Node "nat" []

instance AType Syntax where
  bool = Pbool
  nat = Pnat
  wild = T.Node "_" []

instance (MonadThrow m) => AVal (ContextOf m) where
  atrue = Tagged $ \_ -> return bool
  afalse = Tagged $ \_ -> return bool
  azero = Tagged $ \_ -> return nat
  asucc m = Tagged $ \ctx -> typecheck @"context" ctx m nat

instance (MonadThrow m) => AExp (ContextOf m) where
  aif b exp1 exp2 = Tagged go where
    go ctx = do
      tb <- typecheck @"context" ctx b bool
      t1 <- typeof @"context" ctx exp1
      typecheck @"context" ctx exp2 t1
  apred exp = Tagged $ \ctx -> typecheck @"context" ctx exp nat
  aisZero exp = Tagged go where
    go ctx = seq (typecheck @"context" ctx exp nat) $ return bool

--

instance AVal CBV where
  atrue = Tagged atrue
  afalse = Tagged afalse
  azero = Tagged azero
  asucc m = Tagged $ asucc $ unTagged m

instance AExp CBV where
  aif b exp1 exp2
    | unTagged b == Ptrue = exp1
    | unTagged b == Pfalse = exp2
    | otherwise =
      let b' = unTagged b in
      if b == Tagged b' then Tagged $ Pif (unTagged b) (unTagged exp1) (unTagged exp2)
      else aif (Tagged b') exp1 exp2
  apred m = case cbv m of
    Psucc m' -> Tagged m'
    Pzero -> azero
    m' -> Tagged $ Ppred m'
  aisZero m = case cbv m of
    Pzero -> atrue
    Psucc _ -> afalse
    m' -> Tagged $ PisZero m'

