{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
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
import Data.Tagged
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

typeof :: Tagged (s :: Symbol) typ -> typ
typeof = unTagged

typecheck :: (Show typ, Eq typ) => Tagged (s :: Symbol) typ -> typ -> typ
typecheck exp typ =
  let te = typeof exp in
  case te == typ of
    True -> typ
    False -> terror exp typ te

instance (AType typ, Show typ, Eq typ) => AVal (Tagged "typecheck_simpl" typ) where
  atrue = Tagged bool
  afalse = Tagged bool
  azero = Tagged nat
  asucc m = Tagged $ typecheck m nat

instance (AType typ, Show typ, Eq typ) => AExp (Tagged "typecheck_simpl" typ) where
  aif b exp1 exp2 =
    let tb = typecheck b bool in
    let t1 = typeof exp1 in
    Tagged $ typecheck exp2 t1
  apred exp = Tagged $ typecheck exp nat
  aisZero exp =
    case typecheck exp nat of
      z | z == nat -> Tagged bool

instance (AType typ, Show typ, Eq typ) => AVal (Tagged "typecheck" (r -> typ)) where
  atrue = Tagged $ \_ -> bool
  afalse = Tagged $ \_ -> bool
  azero = Tagged $ \_ -> nat
  asucc m = Tagged $ \r -> typecheck (($ r) <$> m) nat

instance (AType typ, Show typ, Eq typ) => AExp (Tagged "typecheck" (r -> typ)) where
  aif b exp1 exp2 = Tagged go where
    go ctx =
      let tb = typecheck (($ ctx) <$> b) bool in
      let t1 = typeof (($ ctx) <$> exp1) in
      typecheck (($ ctx) <$> exp2) t1
  apred exp = Tagged $ \r -> typecheck (($ r) <$> exp) nat
  aisZero exp = Tagged go where
    go ctx =
      case typecheck (($ ctx) <$> exp) nat of
        z | z == nat -> bool

