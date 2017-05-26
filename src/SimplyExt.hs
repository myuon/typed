{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module SimplyExt where

import Debug.Trace
import Control.Monad
import Control.Monad.Catch
import Data.Tagged
import Data.List (elemIndex, nub, lookup)
import qualified Data.Tree as T
import qualified Data.Map as M
import Init
import AExp
import Untyped hiding (Var, uisVal)
import Simply

class (SpType typ) => SpExtType typ where
  baseA :: typ
  unit :: typ
  tuple :: typ -> typ -> typ
  record :: [(String, typ)] -> typ
  coprod :: typ -> typ -> typ
  variant :: [(String, typ)] -> typ
  list :: typ -> typ

pattern PbaseA = T.Node "A" []
pattern Punit = T.Node "Unit" []
pattern Ptuple exp1 exp2 = T.Node "tuple" [exp1, exp2]
pattern Precord es = T.Node "record" es
pattern Precord_at label x = T.Node label [x]
pattern Pcoprod exp1 exp2 = T.Node "sum" [exp1, exp2]
pattern Pvariant es = T.Node "variant" es
pattern Plist x = T.Node "list" [x]

instance SpExtType Syntax where
  baseA = PbaseA
  unit = Punit
  tuple = Ptuple
  record m = Precord $ fmap (\(l,x) -> Precord_at l x) m
  coprod = Pcoprod
  variant m = Pvariant $ fmap (\(l,x) -> Precord_at l x) m
  list = Plist

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
  inL_as :: repr -> typ -> repr
  inR_as :: repr -> typ -> repr
  case_coprod :: repr -> var -> repr -> var -> repr -> repr
  tagging :: String -> repr -> typ -> repr
  case_variant :: repr -> [(String, var, repr)] -> repr
  fixpoint :: repr -> repr -> repr
  nil_as :: typ -> repr
  cons_as :: typ -> repr -> repr -> repr
  isnil_as :: typ -> repr -> repr
  head_as :: typ -> repr -> repr
  tail_as :: typ -> repr -> repr

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
pattern PinL_as exp ty = T.Node "inL_as" [exp, ty]
pattern PinR_as exp ty = T.Node "inR_as" [exp, ty]
pattern Pcase_coprod exp x expL y expR = T.Node "case_coprod" [exp, V x, expL, V y, expR]
pattern Ptagging label exp typ = T.Node "tagging" [T.Node label [], exp, typ]
pattern Pcase_variant exp cases = T.Node "case_variant" [exp, T.Node "cases" cases]
pattern Pfix exp exp2 = T.Node "fix" [exp, exp2]
pattern Pnil_as ty = T.Node "nil" [ty]
pattern Pcons_as ty exp1 exp2 = T.Node "cons" [ty, exp1, exp2]
pattern Pisnil_as ty exp = T.Node "isnil" [ty, exp]
pattern Phead_as ty exp = T.Node "head" [ty, exp]
pattern Ptail_as ty exp = T.Node "tail" [ty, exp]

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
  inL_as = PinL_as
  inR_as = PinR_as
  case_coprod exp x expL y expR = Pcase_coprod exp (show x) expL (show y) expR
  tagging = Ptagging
  case_variant exp cases = Pcase_variant exp $ fmap (\(label,v,r) -> T.Node label [V $ show v,r]) cases
  fixpoint = Pfix
  nil_as = Pnil_as
  cons_as = Pcons_as
  isnil_as = Pisnil_as
  head_as = Phead_as
  tail_as = Ptail_as

--

instance (MonadThrow m) => SpExtExp Int Syntax (ContextOf m) where
  star = Tagged $ \_ -> return unit
  exp1 ## exp2 = Tagged go where
    go ctx = seq (typecheck @"context" ctx exp1 unit) $ typeof @"context" ctx exp2
  typeAs exp ty = Tagged go where
    go ctx = typecheck @"context" ctx exp ty
  letin v exp1 exp2 = Tagged go where
    go ctx = do
      typ1 <- typeof @"context" ctx exp1
      typeof @"context" ((v , VarBind typ1) .: ctx) exp2
  pair exp1 exp2 = Tagged go where
    go ctx = do
      ty1 <- typeof @"context" ctx exp1
      ty2 <- typeof @"context" ctx exp2
      return $ tuple ty1 ty2
  _1 exp = Tagged go where
    go ctx = do
      ty' <- typeof @"context" ctx exp
      case ty' of
        Ptuple ty1 _ -> return ty1
        z -> terror (unTagged exp ctx) (show $ Ptuple wild wild) (show z)
  _2 exp = Tagged go where
    go ctx = do
      ty' <- typeof @"context" ctx exp
      case ty' of
        Ptuple _ ty2 -> return ty2
        z -> terror (unTagged exp ctx) (show $ Ptuple wild wild) (show z)
  fields es = Tagged go where
    go ctx = do
      let labels = fmap fst es
      typs <- mapM (typeof @"context" ctx) $ fmap snd es
      return $ record $ zip labels typs
  proj_label label rc = Tagged go where
    go ctx =
      typeof @"context" ctx rc >>=
      \case
        Precord tys ->
          case elemIndex label (fmap (\(Pfield_at l _) -> l) tys) of
            Just n -> return $ (\(Pfield_at _ x) -> x) $ tys !! n
            Nothing -> throwM' $ (show $ Precord tys) `should` ("contain " ++ label)
        z -> terror (unTagged rc ctx) (show $ Precord [wild]) (show z)
  inL_as exp ty = Tagged go where
    go ctx = do
      tyL <- typeof @"context" ctx exp
      case ty of
        Pcoprod ty1 ty2 | ty1 == tyL -> return $ coprod ty1 ty2
        z -> terror (unTagged exp ctx) (show $ coprod tyL wild) (show z)
  inR_as exp ty = Tagged go where
    go ctx = do
      tyR <- typeof @"context" ctx exp
      case ty of
        Pcoprod ty1 ty2 | ty2 == tyR -> return $ coprod ty1 ty2
        z -> terror (unTagged exp ctx) (show $ coprod wild tyR) (show z)
  case_coprod exp x expL y expR = Tagged go where
    go ctx =
      typeof @"context" ctx exp >>=
      \case
        Pcoprod ty1 ty2 -> do
          tyL <- typeof @"context" ((x, VarBind ty1) .: ctx) expL
          typecheck @"context" ((y, VarBind ty2) .: ctx) expR tyL
        z -> terror (unTagged exp ctx) (show $ Pcoprod wild wild) (show z)
  tagging label exp ty = Tagged go where
    go ctx =
      case ty of
        Pvariant vs -> do
          tyl <- typeof @"context" ctx exp
          if Pfield_at label tyl `elem` vs
            then return $ Pvariant vs
            else terror (unTagged exp ctx) (show tyl) (show $ Pvariant [wild])
        z -> terror (unTagged exp ctx) (show $ Pvariant [wild]) (show z)
  case_variant exp vs = Tagged go where
    go ctx =
      typeof @"context" ctx exp >>=
      \case
        Pvariant vs' | fmap (\(T.Node l _) -> l) vs' == fmap (\(l,_,_) -> l) vs -> do
          tys <- mapM (\(label,v,r) -> typeof @"context" ((v, VarBind $ (\(Just x) -> x) $ lookup label $ fmap (\(Precord_at l x) -> (l,x)) vs') .: ctx) r) vs
          case nub tys of
            [x] -> return x
            z -> throwM' $ show (fmap (\(l,v,x) -> (l,v,Pstar)) vs) `should` ("have same codomain, but " ++ show z)
        z -> terror (unTagged exp ctx) (show $ fmap (\(l,_,_) -> T.Node l []) vs) (show z)
  fixpoint exp exp2 = Tagged go where
    go ctx =
      typeof @"context" ctx exp >>=
      \case
        Parrow ty1 ty2 | ty1 == ty2 -> typecheck @"context" ctx exp2 ty1
        Parrow ty1 ty2 -> terror (unTagged exp ctx) (show $ arrow ty1 ty1) (show $ arrow ty1 ty2)
        z -> terror (unTagged exp ctx) (show $ Parrow wild wild) (show z)
  nil_as typ = Tagged go where
    go ctx = return $ list typ
  cons_as typ exp1 exp2 = Tagged go where
    go ctx =
      seq (typecheck @"context" ctx exp1 typ) $
      typecheck @"context" ctx exp2 (list typ)
  isnil_as typ exp = Tagged go where
    go ctx =
      seq (typecheck @"context" ctx exp (list typ)) $ return bool
  head_as typ exp = Tagged go where
    go ctx =
      seq (typecheck @"context" ctx exp (list typ)) $ return typ
  tail_as typ exp = Tagged go where
    go ctx = typecheck @"context" ctx exp (list typ)

--

-- isVal in SpExtExp
-- should be polymorphic in calculus typeclasses?
spisVal :: Syntax -> Bool
spisVal Pstar = True
spisVal (Ppair x1 x2) = spisVal x1 && spisVal x2
spisVal (Pfields xs) = all spisVal xs
spisVal (PinL_as t _) = spisVal t
spisVal (PinR_as t _) = spisVal t
spisVal (Pfix _ _) = True
spisVal k = sisVal k

instance Subst SpExtExp Int CBV where
  subst v sb = go where
    go' = unTagged . go . Tagged
    
    go :: CBV -> CBV
    go (Tagged Pstar) = Tagged Pstar
    go (Tagged (Pletin v' t1 t2)) = Tagged $ Pletin v' (go' t1) (go' t2)
    go (Tagged (Ppair t1 t2)) = Tagged $ Ppair (go' t1) (go' t2)
    go (Tagged (P_1 t)) = Tagged $ P_1 $ go' t
    go (Tagged (P_2 t)) = Tagged $ P_2 $ go' t
    go (Tagged (PinL_as t ty)) = Tagged $ PinL_as (go' t) ty
    go (Tagged (PinR_as t ty)) = Tagged $ PinR_as (go' t) ty
    go (Tagged (Pcase_coprod t x tx y ty)) = Tagged $ Pcase_coprod (go' t) x (go' tx) y (go' ty)
    go z = subst @SpExp v sb z

instance SpExtExp Int Syntax CBV where
  star = Tagged Pstar

  typeAs m ty
    | sisVal m = m
    | otherwise = Tagged $ typeAs (cbv m) ty
  letin v t1 t2
    | sisVal t1 = subst @SpExtExp v t1 t2
    | otherwise =
      let t1' = cbv t1 in
      if t1 == Tagged t1' then Tagged $ Pletin (show v) t1' (cbv t2)
      else letin v (Tagged t1') t2
  pair t1 t2
    | sisVal t1 =
      let t2' = cbv t2 in
      if t2 == Tagged t2' then Tagged $ Ppair (cbv t1) t2'
      else pair t1 (Tagged t2')
    | otherwise =
      let t1' = cbv t1 in
      if t1 == Tagged t1' then Tagged $ Ppair t1' (cbv t2)
      else pair (Tagged t1') t2
  _1 t =
    case cbv t of
      Ppair v1 v2 | sisVal v1 && sisVal v2 -> Tagged v1
      t' -> if t == Tagged t' then Tagged $ P_1 t' else _1 (Tagged t')
  _2 t =
    case cbv t of
      Ppair v1 v2 | sisVal v1 && sisVal v2 -> Tagged v2
      t' -> if t == Tagged t' then Tagged $ P_2 t' else _2 (Tagged t')
  fields ts =
    let ts' = fmap (\(l,t) -> (l,cbv t)) ts in
    if ts == fmap (\(l,t) -> (l,Tagged t)) ts' then Tagged $ Pfields $ fmap (\(l,t) -> Pfield_at l (cbv t)) ts else fields (fmap (\(l,t) -> (l,Tagged t)) ts')
  proj_label label t =
    case cbv t of
      Pfields fs | all (\(Pfield_at _ t) -> spisVal t) fs -> 
        case elemIndex label (fmap (\(Pfield_at l _) -> l) fs) of
          Just n -> Tagged $ (\(Pfield_at _ x) -> x) $ fs !! n
      t' -> if t == Tagged t' then Tagged $ Pproj_label label t' else proj_label label (Tagged t')
  inL_as t ty =
    let t' = cbv t in
    if t == Tagged t' then Tagged $ PinL_as t' ty else inL_as (Tagged t') ty
  inR_as t ty =
    let t' = cbv t in
    if t == Tagged t' then Tagged $ PinR_as t' ty else inR_as (Tagged t') ty
  case_coprod t x tx y ty =
    case cbv t of
      PinL_as v _ | spisVal v -> subst @SpExtExp x (Tagged v) tx
      PinR_as v _ | spisVal v -> subst @SpExtExp y (Tagged v) ty
      t' ->
        if t == Tagged t' then Tagged $ Pcase_coprod t' (show x) (cbv tx) (show y) (cbv ty)
        else case_coprod (Tagged t') x ty y ty
  tagging label t ty =
    let t' = cbv t in
    if t == Tagged t' then Tagged $ Ptagging label t' ty else tagging label (Tagged t') ty
  case_variant t vs =
    case cbv t of
      Ptagging label v ty | spisVal v ->
        case elemIndex label (fmap (\(l,_,_) -> l) vs) of
          Just n -> (\(_,x,t) -> subst @SpExtExp x (Tagged v) t) $ vs !! n
      t' -> if t == Tagged t' then Tagged $ Pcase_variant t' $ fmap (\(l,x,t) -> T.Node l [V $ show x, unTagged t]) vs
            else case_variant (Tagged t') vs

{-
  we need some kind of `lazy-evaluation` to define a fixpoint operator


  fixpoint t1 t2 =
    case cbv t1 of
      z@(PabsT x ty (PabsT y ty' t1')) -> subst @SpExtExp (read x) (fixpoint (Tagged z) t2) $ subst @SpExtExp (read y) t2 (Tagged t1')
      t' -> if t1 == Tagged t' then Tagged $ Pfix t' (cbv t2) else fixpoint (Tagged t') t2
-}
