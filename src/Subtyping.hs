{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Subtyping where

import Control.Monad.Catch
import Data.Tagged
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Simply

--

instance (MonadThrow m) => AVal (SubContextOf m) where
  atrue = Tagged $ \_ -> return bool
  afalse = Tagged $ \_ -> return bool
  azero = Tagged $ \_ -> return nat
  asucc m = Tagged $ \ctx -> typecheck @"subcontext" ctx m nat

instance (MonadThrow m) => AExp (SubContextOf m) where
  aif b exp1 exp2 = Tagged go where
    go ctx = do
      tb <- typecheck @"subcontext" ctx b bool
      t1 <- typeof @"subcontext" ctx exp1
      typecheck @"subcontext" ctx exp2 t1
  apred exp = Tagged $ \ctx -> typecheck @"subcontext" ctx exp nat
  aisZero exp = Tagged go where
    go ctx = seq (typecheck @"subcontext" ctx exp nat) $ return bool

--

class SpType typ => SubType typ where
  top :: typ
  record :: [(String, typ)] -> typ

  subtype :: typ -> typ -> Bool

pattern Ptop = T.Node "Top" []
pattern Precord t = T.Node "record" t
pattern Precord_at l t = T.Node l [t]

lookupRecord :: String -> T.Forest String -> Maybe Syntax
lookupRecord s = go where
  go [] = Nothing
  go (Precord_at l t : es')
    | l == s = Just t
    | otherwise = go es'

instance SubType Syntax where
  top = Ptop
  record = Precord . fmap (uncurry Precord_at)

  subtype tyS tyT
    | tyS == tyT = True
    | otherwise =
      case (tyS, tyT) of
        (Precord fS, Precord fT) ->
          let check (Precord_at l t) = lookupRecord l fS >>= \ty -> return $ subtype ty t in
          let fromMaybe s = s == Just True in
          all (fromMaybe . check) fT
        (_, Ptop) -> True
        (Parrow ty11 ty12, Parrow ty21 ty22) -> subtype ty21 ty11 && subtype ty12 ty22
        _ -> False

--

class SpExp var typ repr => SubExp var typ repr where
  fields :: [(String, repr)] -> repr
  proj :: repr -> String -> repr

pattern Pfields es = T.Node "fields" es
pattern Pfield_at l t = T.Node l [t]
pattern Pproj t s = T.Node s [t]

instance MonadThrow m => SpExp Int Syntax (SubContextOf m) where
  svar v = Tagged go where
    go ctx
      | M.member v ctx =
        case ctx M.! v of VarBind b -> return b
      | otherwise = throwM' $ notInContext (show v) ctx
  sabs v ty exp = Tagged go where
    go ctx = do
      let ctx' = (v, VarBind ty) .: ctx
      ty' <- typeof @"subcontext" ctx' exp
      return $ arrow ty ty'
  sapp exp1 exp2 = Tagged go where
    go ctx = do
      ty1 <- typeof @"subcontext" ctx exp1
      ty2 <- typeof @"subcontext" ctx exp2
      case ty1 of
        (Parrow ty11 ty12) | ty2 `subtype` ty11 -> return ty12
        t -> terror (unTagged exp1 ctx) (show ty2) (show ty1)
  
instance MonadThrow m => SubExp Int Syntax (SubContextOf m) where
  fields es = Tagged go where
    go ctx = record <$> mapM (\(l,t) -> (,) l <$> typeof @"subcontext" ctx t) es
  proj t label = Tagged go where
    go ctx =
      typeof @"subcontext" ctx t >>=
      \case
        Precord vs ->
          case lookupRecord label vs of
            Just t -> return t
            Nothing -> throwM $ notInRecord @(T.Tree String) label (Precord vs)
        z -> terror (unTagged t ctx) (show $ Precord [wild]) (show z)
  
  
