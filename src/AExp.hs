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

-- value

data AValue
  = ATrue | AFalse
  | AZero | ASucc AValue
  deriving (Eq, Show)

instance AVal AValue where
  atrue = ATrue
  afalse = AFalse
  azero = AZero
  asucc exp = ASucc exp

-- big-step semantics

instance AVal (Tagged "eval" AValue) where
  atrue = Tagged atrue
  afalse = Tagged afalse
  azero = Tagged azero
  asucc (Tagged n) = Tagged $ asucc n

instance AExp (Tagged "eval" AValue) where
  aif b exp1 exp2
    | b == atrue = exp1
    | b == afalse = exp2
  apred exp = case exp of
    Tagged AZero -> azero
    Tagged (ASucc n) -> Tagged n
  aisZero exp = case exp of
    Tagged AZero -> atrue
    Tagged (ASucc _) -> afalse

aeval :: Tagged "eval" AValue -> AValue
aeval = unTagged

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

instance (MonadThrow m) => AVal (Typecheck m) where
  atrue = Tagged $ \_ -> return bool
  afalse = Tagged $ \_ -> return bool
  azero = Tagged $ \_ -> return nat
  asucc m = Tagged $ \ctx -> typecheck ctx m nat

instance (MonadThrow m) => AExp (Typecheck m) where
  aif b exp1 exp2 = Tagged go where
    go ctx = do
      tb <- typecheck ctx b bool
      t1 <- typeof ctx exp1
      typecheck ctx exp2 t1
  apred exp = Tagged $ \ctx -> typecheck ctx exp nat
  aisZero exp = Tagged go where
    go ctx = seq (typecheck ctx exp nat) $ return bool

