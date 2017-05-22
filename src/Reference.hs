{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Reference where

import Control.Monad
import Control.Monad.Catch
import Data.Tagged
import Data.List (elemIndex, nub, lookup)
import qualified Data.Tree as T
import qualified Data.Map as M
import Init
import AExp
import Untyped hiding (Var)
import Simply
import SimplyExt (pattern Punit, pattern Pstar)

class (SpType typ) => RefType typ where
  unit :: typ
  reftype :: typ -> typ

pattern Preftype t = T.Node "reftype" [t]

instance RefType Syntax where
  unit = Punit
  reftype = Preftype

-- AExp, SpExp as RefTypecheck

instance (MonadThrow m) => AVal (RefTypecheck m) where
  atrue = Tagged $ \_ _ -> return bool
  afalse = Tagged $ \_ _ -> return bool
  azero = Tagged $ \_ _ -> return nat
  asucc m = Tagged $ \ctx sto -> reftypecheck ctx sto m nat

instance (MonadThrow m) => AExp (RefTypecheck m) where
  aif b exp1 exp2 = Tagged go where
    go ctx sto = do
      tb <- reftypecheck ctx sto b bool
      t1 <- reftypeof ctx sto exp1
      reftypecheck ctx sto exp2 t1
  apred exp = Tagged $ \ctx sto -> reftypecheck ctx sto exp nat
  aisZero exp = Tagged go where
    go ctx sto = seq (reftypecheck ctx sto exp nat) $ return bool

instance MonadThrow m => SpExp Int Syntax (RefTypecheck m) where
  svar v = Tagged go where
    go ctx sto
      | M.member v ctx =
        case ctx M.! v of VarBind b -> return b
      | otherwise = throwM $ NotInContext (show v) ctx
  sabs v ty exp = Tagged go where
    go ctx sto = do
      let ctx' = (v, VarBind ty) .: ctx
      ty' <- reftypeof ctx' sto exp
      return $ arrow ty ty'
  sapp exp1 exp2 = Tagged go where
    go ctx sto = do
      ty1 <- reftypeof ctx sto exp1
      ty2 <- reftypeof ctx sto exp2
      case ty1 of
        (Parrow ty11 ty12) | ty2 == ty11 -> return ty12
        t -> terror (unTagged exp1 ctx sto) (show ty2) (show ty1)

--

class (SpExp var typ repr) => RefExp var typ repr where
  star :: repr
  loc :: String -> repr
  ref :: repr -> repr
  deref :: repr -> repr
  assign :: repr -> repr -> repr
  (##) :: repr -> repr -> repr

pattern Pref t = T.Node "ref" [t]
pattern Ploc t = T.Node "location" [T.Node t []]
pattern Pderef t = T.Node "!" [t]
pattern Passign t1 t2 = T.Node "assign" [t1,t2]
pattern Pseq t1 t2 = T.Node "##" [t1,t2]

instance RefExp Int Syntax Syntax where
  star = Pstar
  loc = Ploc
  ref = Pref
  deref = Pderef
  assign = Passign
  (##) = Pseq

instance MonadThrow m => RefExp Int Syntax (RefTypecheck m) where
  star = Tagged $ \ctx sto -> return unit
  loc label = Tagged go where
    go ctx sto =
      case M.member label sto of
        True -> return $ reftype $ sto M.! label
        False -> throwM $ NotInStore label sto
  ref exp = Tagged go where
    go ctx sto = reftype <$> reftypeof ctx sto exp
  deref exp = Tagged go where
    go ctx sto =
      reftypeof ctx sto exp >>=
      \case
        Preftype ty -> return ty
        z -> terror (unTagged exp ctx sto) (show $ Preftype wild) (show z)
  assign exp1 exp2 = Tagged go where
    go ctx sto =
      reftypeof ctx sto exp1 >>=
      \case
        Preftype ty -> seq (reftypecheck ctx sto exp2 ty) $ return unit
        z -> terror (unTagged exp2 ctx sto) (show $ Preftype wild) (show z)
  exp1 ## exp2 = Tagged go where
    go ctx sto =
      seq (reftypecheck ctx sto exp1 unit) $ reftypeof ctx sto exp2


