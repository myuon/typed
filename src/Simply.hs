{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Simply where

import Control.Monad
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Untyped hiding (Var)

-- simple types

class (AType typ) => SpType typ where
  arrow :: typ -> typ -> typ

pattern Parrow ty1 ty2 = T.Node "arr" [ty1, ty2]

instance SpType Syntax where
  arrow = Parrow

-- contexts

data Binding typ = VarBind (SpType typ => typ)
instance (Show typ, SpType typ) => Show (Binding typ) where
  show (VarBind t) = show t

type Context = M.Map String (Binding Syntax)

(.:) :: (String, Binding Syntax) -> M.Map String (Binding Syntax) -> M.Map String (Binding Syntax)
(x,bind) .: gs = M.insert x bind gs

-- terms

class (SpType typ) => SpExp var typ repr | repr -> var, repr -> typ where
  svar :: var -> repr
  sabs :: var -> typ -> repr -> repr
  sapp :: repr -> repr -> repr

pattern PabsT v typ exp = T.Node "absT" [V v,typ,exp]

instance SpExp Int Syntax Syntax where
  svar = Pvar . show
  sabs v = PabsT (show v)
  sapp = Papp

-- type inference

class (Show repr, Show typ, SpExp var typ repr, SpType typ) => SpInfer var typ repr where
  inferSp :: Context -> repr -> typ

  typcheckSp :: Eq typ => Context -> repr -> typ -> typ
  typcheckSp ctx exp typ =
    let te = inferSp ctx exp in
    case te == typ of
      True -> typ
      False -> terror exp typ te

instance SpInfer Int Syntax Syntax where
  inferSp ctx = go where
    go (Pvar v)
      | M.member v ctx =
        case ctx M.! v of
          VarBind b -> b
      | otherwise = error $ "Not found " ++ show v ++ " in " ++ show ctx
    go (PabsT v ty exp) =
      let ctx' = (v, VarBind ty) .: ctx in
      let ty' = inferSp ctx' exp in
      arrow ty ty'
    go (Papp exp1 exp2) =
      let ty1 = inferSp ctx exp1 in
      let ty2 = inferSp ctx exp2 in
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> ty12
        t -> terror exp1 ty2 ty1
    go exp = inferA exp
