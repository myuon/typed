{-# LANGUAGE DataKinds #-}
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
import Data.Tagged
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Untyped hiding (Var)

-- simply typed

class (AType typ) => SpType typ where
  arrow :: typ -> typ -> typ

pattern Parrow ty1 ty2 = T.Node "arr" [ty1, ty2]

instance SpType Syntax where
  arrow = Parrow

-- contexts

data Binding typ = VarBind (SpType typ => typ)
instance (Show typ, SpType typ) => Show (Binding typ) where
  show (VarBind t) = show t

type Context a = M.Map Int (Binding a)

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

instance SpExp Int Syntax (Tagged "typecheck" (Context Syntax -> Syntax)) where
  svar v = Tagged go where
    go ctx
      | M.member v ctx =
        case ctx M.! v of VarBind b -> b
      | otherwise = error $ "Not found " ++ show v ++ " in " ++ show ctx
  sabs v ty exp = Tagged go where
    go ctx =
      let ctx' = (v, VarBind ty) .: ctx in
      let ty' = typeof exp ctx' in
      arrow ty ty'
  sapp exp1 exp2 = Tagged go where
    go ctx =
      let ty1 = typeof exp1 ctx in
      let ty2 = typeof exp2 ctx in
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> ty12
        t -> terror (unTagged exp1 ctx) ty2 ty1
