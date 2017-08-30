{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Lambda.Recon.Simply where

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Tagged

import Preliminary.Types
import Lambda.Explicit.Simply

instance MonadThrow m => SpExp Int Syntax (ConstrOf m) where
  svar v = Tagged go where
    go ctx
      | M.member v ctx =
        case ctx M.! v of VarBind b -> return (b, [], [])
      | otherwise = throwM' $ notInContext (show v) ctx
  sabs v ty exp = Tagged go where
    go ctx = do
      let ctx' = (v, VarBind ty) .: ctx
      (ty', tvs, con) <- typeof @"constr" ctx' exp
      return (arrow ty ty', tvs, con)
  sapp exp1 exp2 = Tagged go where
    go ctx = do
      (ty1, tvs1, con1) <- typeof @"constr" ctx exp1
      (ty2, tvs2, con2) <- typeof @"constr" ctx exp2
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> return (ty12, tvs1, con1)
        t -> terror ((\(a,_,_) -> a) <$> unTagged exp1 ctx) (show ty2) (show ty1)


