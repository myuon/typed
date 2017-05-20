{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module SimplyExt where

import Control.Monad
import Data.Tagged
import GHC.TypeLits
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Untyped hiding (Var)
import Simply

class (SpType typ) => SpExtType typ where
  baseA :: typ
  unit :: typ
  tuple :: typ -> typ -> typ
  record :: [(String, typ)] -> typ

pattern PbaseA = T.Node "A" []
pattern Punit = T.Node "Unit" []
pattern Ptuple exp1 exp2 = T.Node "tuple" [exp1, exp2]
pattern Precord es = T.Node "record" es
pattern Precord_at label x = T.Node label [x]

instance SpExtType Syntax where
  baseA = PbaseA
  unit = Punit
  tuple = Ptuple
  record m = Precord $ fmap (\(l,x) -> Precord_at l x) m

--

class (SpExp var typ repr) => SpExtExp var typ repr where
  star :: repr
  (##) :: repr -> repr -> repr
  typeAs :: repr -> typ -> repr
  letin :: var -> repr -> repr -> repr
  pair :: repr -> repr -> repr
  _1 :: repr -> repr
  _2 :: repr -> repr
  fields :: [(String, repr)] -> repr
  proj_label :: String -> repr -> repr

pattern Pstar = T.Node "*" []
pattern Pseq exp1 exp2 = T.Node "##" [exp1, exp2]
pattern PtypeAs exp ty = T.Node "as" [exp, ty]
pattern Pletin v exp1 exp2 = T.Node "let" [V v, exp1, exp2]
pattern Ppair exp1 exp2 = T.Node "pair" [exp1, exp2]
pattern P_1 exp = T.Node "_1" [exp]
pattern P_2 exp = T.Node "_2" [exp]
pattern Pfields es = T.Node "fields" es
pattern Pfield_at label x = T.Node label [x]
pattern Pproj_label label exp = T.Node "proj_label" [T.Node label [], exp]

instance SpExtExp Int Syntax Syntax where
  star = Pstar
  (##) = Pseq
  typeAs = PtypeAs
  letin k = Pletin (show k)
  pair = Ppair
  _1 = P_1
  _2 = P_2
  fields ms = Pfields $ fmap (\(l,x) -> Pfield_at l x) ms
  proj_label = Pproj_label

--

instance SpExtExp Int Syntax (Tagged "typecheck" (Context Syntax -> Syntax)) where
  star = Tagged $ \_ -> unit
  exp1 ## exp2 = Tagged go where
    go ctx =
      let Punit = typeof exp1 ctx in
      typeof exp2 ctx
  typeAs exp ty = Tagged go where
    go ctx =
      case typeof exp ctx of
        z | z == ty -> ty
  letin v exp1 exp2 = Tagged go where
    go ctx =
      let typ1 = typeof exp1 ctx in
      typeof exp2 ((v , VarBind typ1) .: ctx)
  pair exp1 exp2 = Tagged go where
    go ctx =
      let ty1 = typeof exp1 ctx in
      let ty2 = typeof exp2 ctx in
      tuple ty1 ty2
  _1 exp = Tagged go where
    go ctx =
      let Ptuple ty1 _ = typeof exp ctx in
      ty1
  _2 exp = Tagged go where
    go ctx =
      let Ptuple _ ty2 = typeof exp ctx in
      ty2
  fields es = Tagged go where
    go ctx =
      let tys = fmap (\(_,x) -> typeof x ctx) es in
      record $ zip (fmap fst es) tys
  proj_label label rc = Tagged go where
    go ctx =
      let Precord tys = typeof rc ctx in
      snd $ head $ filter (\x -> fst x == label) $ fmap (\(Pfield_at l x) -> (l,x)) tys

