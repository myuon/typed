{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Simply where

import Control.Monad.Catch
import Data.Tagged
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Untyped hiding (Var, uisVal)

-- simply typed

class (AType typ) => SpType typ where
  arrow :: typ -> typ -> typ

pattern Parrow ty1 ty2 = T.Node "arr" [ty1, ty2]

instance SpType Syntax where
  arrow = Parrow

-- terms

class (SpType typ) => SpExp var typ repr | repr -> var, repr -> typ where
  svar :: var -> repr
  sabs :: var -> typ -> repr -> repr
  sapp :: repr -> repr -> repr

  sisVal :: repr -> Bool

pattern PabsT v typ exp = T.Node "absT" [V v,typ,exp]

instance SpExp Int Syntax Syntax where
  svar = Pvar . show
  sabs v = PabsT (show v)
  sapp = Papp

  sisVal Ptrue = True
  sisVal Pfalse = True
  sisVal Pzero = True
  sisVal (Psucc k) = sisVal k
  sisVal (PabsT _ _ _) = True
  sisVal _ = False

-- type inference

instance MonadThrow m => SpExp Int Syntax (ContextOf m) where
  svar v = Tagged go where
    go ctx
      | M.member v ctx =
        case ctx M.! v of VarBind b -> return b
      | otherwise = throwM' $ notInContext (show v) ctx
  sabs v ty exp = Tagged go where
    go ctx = do
      let ctx' = (v, VarBind ty) .: ctx
      ty' <- typeof @"context" ctx' exp
      return $ arrow ty ty'
  sapp exp1 exp2 = Tagged go where
    go ctx = do
      ty1 <- typeof @"context" ctx exp1
      ty2 <- typeof @"context" ctx exp2
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> return ty12
        t -> terror (unTagged exp1 ctx) (show ty2) (show ty1)

-- eval

instance Subst SpExp Int CBV where
  subst v term = go where
    go' = unTagged . go . Tagged
    
    go :: CBV -> CBV
    go (Tagged Ptrue) = Tagged Ptrue
    go (Tagged Pfalse) = Tagged Pfalse
    go (Tagged Pzero) = Tagged Pzero
    go (Tagged (Psucc t)) = Tagged $ Psucc $ go' t
    go (Tagged (Pif b t1 t2)) = Tagged $ Pif (go' b) (go' t1) (go' t2)
    go (Tagged (Ppred t)) = Tagged $ Ppred $ go' t
    go (Tagged (PisZero t)) = Tagged $ PisZero $ go' t
    
    go (Tagged (Pvar x))
      | x == show v = term
      | otherwise = svar $ read x
    go (Tagged (PabsT x typ exp)) = Tagged $ PabsT x typ $ go' exp
    go (Tagged (Papp m1 m2)) = Tagged $ Papp (go' m1) (go' m2)

instance SpExp Int Syntax CBV where
  sisVal (Tagged t) = sisVal t
  
  svar v = Tagged $ Pvar $ show v
  sabs v ty m = Tagged $ PabsT (show v) ty $ unTagged m
  sapp m1 m2 =
    case unTagged m1 of
      PabsT v _ m1' | sisVal m2 -> subst @SpExp (read v) m2 (Tagged m1')
      _ | sisVal m1 -> 
        let m2' = Tagged @"cbv" $ unTagged m2 in
        if unTagged m2 == unTagged m2' then Tagged $ Papp (unTagged m1) (unTagged m2)
        else uapp m1 m2'
      _ ->
        let m1' = Tagged @"cbv" $ unTagged m1 in
        if unTagged m1 == unTagged m1' then Tagged $ Papp (unTagged m1) (unTagged m2)
        else uapp m1' m2

