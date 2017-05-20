{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module AExp where

import Control.Monad
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Set as S
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

class (AExp repr, AVal val) => AEval repr val where
  aeval :: repr -> val

instance AEval Syntax AValue where
  aeval = go where
    go :: Syntax -> AValue
    go Ptrue = atrue
    go Pfalse = afalse
    go Pzero = azero
    go (Pif b exp1 exp2) =
      case go b of
        ATrue -> go exp1
        AFalse -> go exp2
    go (Psucc exp) = ASucc (go exp)
    go (Ppred exp) =
      case go exp of
        AZero -> AZero
        ASucc n -> n
    go (PisZero exp) =
      case go exp of
        AZero -> ATrue
        ASucc _ -> AFalse
    go exp = error $ "Not match any case: " ++ show exp

-- types

class AType typ where
  bool :: typ
  nat :: typ

pattern Pbool = T.Node "bool" []
pattern Pnat = T.Node "nat" []

instance AType Syntax where
  bool = Pbool
  nat = Pnat

terror :: (Show repr, Show typ) => repr -> typ -> typ -> a
terror m exp act = error $ concat
  [ "TypeError> "
  , "`" ++ show m ++ "`"
  , " : Expected "
  , show exp
  , " , Actual "
  , show act
  ]

class (Show repr, Show typ, AExp repr, AType typ) => AInfer repr typ where
  inferA :: repr -> typ

  typcheckA :: Eq typ => repr -> typ -> typ
  typcheckA exp typ =
    let te = inferA exp in
    case te == typ of
      True -> typ
      False -> terror exp typ te

instance AInfer Syntax Syntax where
  inferA Ptrue = bool
  inferA Pfalse = bool
  inferA (Pif b exp1 exp2) =
    let tb = typcheckA b Pbool in
    let t1 = inferA @Syntax @Syntax exp1 in
    typcheckA exp2 t1
  inferA Pzero = nat
  inferA (Psucc exp) = typcheckA exp Pnat
  inferA (Ppred exp) = typcheckA exp Pnat
  inferA (PisZero exp) = let Pnat = typcheckA exp Pnat in Pbool
  inferA z = error $ "Unexpected syntax tree: " ++ show z


