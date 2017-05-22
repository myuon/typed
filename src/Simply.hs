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
import Untyped hiding (Var)

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

pattern PabsT v typ exp = T.Node "absT" [V v,typ,exp]

instance SpExp Int Syntax Syntax where
  svar = Pvar . show
  sabs v = PabsT (show v)
  sapp = Papp

-- type inference

instance MonadThrow m => SpExp Int Syntax (Typecheck m) where
  svar v = Tagged go where
    go ctx
      | M.member v ctx =
        case ctx M.! v of VarBind b -> return b
      | otherwise = throwM' $ notInContext (show v) ctx
  sabs v ty exp = Tagged go where
    go ctx = do
      let ctx' = (v, VarBind ty) .: ctx
      ty' <- typeof ctx' exp
      return $ arrow ty ty'
  sapp exp1 exp2 = Tagged go where
    go ctx = do
      ty1 <- typeof ctx exp1
      ty2 <- typeof ctx exp2
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> return ty12
        t -> terror (unTagged exp1 ctx) (show ty2) (show ty1)
