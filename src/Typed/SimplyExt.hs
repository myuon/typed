module Typed.SimplyExt
  ( module Typed.Simply
  , pattern Kbase
  , pattern Tunit
  , pattern Kunit
  , pattern (:.)
  , pattern Tas
  , pattern Tlet
  , pattern Tpair
  , pattern Tpr1
  , pattern Tpr2
  , pattern Kpair
  , pattern Ttuple
  , pattern Tproj
  , pattern Ktuple
  , Term(SimplyExtTerm)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Preliminaries
import Typed.Simply

pattern Kbase = T.Node "A" []

pattern Kunit = T.Node "Unit" []
pattern Tunit = T.Node "unit" []
pattern (:.) tx ty = (Tabs "*" Kunit ty) `Tapp` tx

pattern Tas t typ = T.Node "as" [t,typ]

pattern Tlet x t1 t2 = T.Node "let _ = _ in _" [Tval x,t1,t2]

pattern Tpair x y = T.Node "{_,_}" [x,y]
pattern Tpr1 x = T.Node "_.1" [x]
pattern Tpr2 x = T.Node "_.2" [x]
pattern Kpair x y = T.Node "(_,_)" [x,y]

pattern Ttuple xs = T.Node "{_}" xs
pattern Tproj i t = T.Node i [t]
pattern Ktuple xs = T.Node "(_)" xs

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  | ExpectedType StrTree StrTree
  deriving Show

instance Exception TypeOfError

instance Calculus "simply-ext" StrTree StrTree (M.Map Var Binding) where
  newtype Term "simply-ext" StrTree = SimplyExtTerm StrTree deriving (Eq, Show)

  isValue (SimplyExtTerm t) = go t where
    go Tunit = True
    go (Tpair t1 t2) = go t1 && go t2
    go (Ttuple ts) = all (isValue . SimplyExtTerm) ts
    go t = isValue (SimplyTerm t)

  typeof ctx (SimplyExtTerm t) = go ctx t where
    go ctx Ttrue = return Kbool
    go ctx Tfalse = return Kbool
    go ctx (Tif t a b) = do
      tt <- go ctx t
      case tt of
        Kbool -> do
          ta <- go ctx a
          tb <- go ctx b
          if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        _ -> throwM GuardOfConditionalNotABoolean
    go ctx Tzero = return Knat
    go ctx (Tsucc t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat
    go ctx (Tpred t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat
    go ctx (Tiszero t) = do
      tt <- go ctx t
      case tt of
        Knat -> return Knat
        _ -> throwM ExpectedANat
    go ctx (Tvar x) = case ctx M.! x of
      NameBind -> throwM WrongKindOfBindingForVariable
      VarBind typ -> return typ
    go ctx (Tabs x xt t) = do
      let ctx' = M.insert x (VarBind xt) ctx
      tt <- go ctx' t
      return $ Karr xt tt
    go ctx (Tapp tx ty) = do
      txTyp <- go ctx tx
      tyTyp <- go ctx ty
      case txTyp of
        Karr txTyp1 txTyp2 ->
          if tyTyp == txTyp1 then return txTyp2
          else throwM ParameterTypeMismatch
        _ -> throwM ArrowTypeExpected
    go ctx Tunit = return Kunit
    go ctx (Tas t typ) = do
      tt <- go ctx t
      if tt == typ
        then return typ
        else throwM $ ExpectedType typ tt
    go ctx (Tlet x t1 t2) = do
      t1T <- go ctx t1
      t2T <- go (M.insert x (VarBind t1T) ctx) t2
      return t2T
    go ctx (Tpair t1 t2) = Kpair <$> go ctx t1 <*> go ctx t2
    go ctx (Tpr1 t) = do
      tT <- go ctx t
      case tT of
        Kpair tT1 tT2 -> return tT1
        z -> throwM $ ExpectedType (Kpair (T.Node "_" []) (T.Node "_" [])) z
    go ctx (Tpr2 t) = do
      tT <- go ctx t
      case tT of
        Kpair tT1 tT2 -> return tT2
        z -> throwM $ ExpectedType (Kpair (T.Node "_" []) (T.Node "_" [])) z
    go ctx (Ttuple ts) = do
      tsTs <- mapM (\t -> go ctx t) ts
      return $ Ktuple tsTs
    go ctx (Tproj i t) = do
      tT <- go ctx t
      case tT of
        Ktuple tTs -> return $ tTs !! (read i)
        z -> throwM $ ExpectedType (Ktuple []) z

  eval1 ctx (SimplyExtTerm t) = fmap SimplyExtTerm $ go ctx t where
    go ctx (Tif Ttrue t1 t2) = return t1
    go ctx (Tif Tfalse t1 t2) = return t2
    go ctx (Tif t1 t2 t3) = do
      t1' <- go ctx t1
      return $ Tif t1' t2 t3
    go ctx (Tsucc t) = do
      t' <- go ctx t
      return $ Tsucc t'
    go ctx (Tpred Tzero) = return Tzero
    go ctx (Tpred (Tsucc n)) | isNat n = return n
    go ctx (Tpred t) = do
      t' <- go ctx t
      return $ Tpred t'
    go ctx (Tiszero Tzero) = return Ttrue
    go ctx (Tiszero (Tsucc n)) | isNat n = return Tfalse
    go ctx (Tiszero t) = do
      t' <- go ctx t
      return $ Tiszero t'
    go ctx (Tvar x) = return $ Tvar x
    go ctx (Tabs x xt t) = return $ Tabs x xt t
    go ctx (Tapp (Tabs x typ11 t12) v) | isValue (SimplyExtTerm v) = return $ subst x v t12
    go ctx (Tapp tx ty)
      | isValue (SimplyTerm tx) = do
        ty' <- go ctx ty
        return $ Tapp tx ty'
      | otherwise = do
        tx' <- go ctx tx
        return $ Tapp tx' ty
    go ctx (Tas v typ)
      | isValue (SimplyExtTerm v) = return v
      | otherwise = fmap (\t -> Tas t typ) $ go ctx v
    go ctx (Tlet x v t)
      | isValue (SimplyExtTerm v) = return $ subst x v t
      | otherwise = do
        v' <- go ctx v
        return $ Tlet x v t
    go ctx (Tpr1 (Tpair v1 v2)) | isValue (SimplyExtTerm v1) && isValue (SimplyExtTerm v2) = return v1
    go ctx (Tpr2 (Tpair v1 v2)) | isValue (SimplyExtTerm v1) && isValue (SimplyExtTerm v2) = return v2
    go ctx (Tpr1 t) = Tpr1 <$> (go ctx t)
    go ctx (Tpr2 t) = Tpr2 <$> (go ctx t)
    go ctx (Tpair t1 t2)
      | isValue (SimplyExtTerm t1) = Tpair t1 <$> go ctx t2
      | otherwise = Tpair <$> (go ctx t1) <*> return t2
    go ctx (Tproj i (Ttuple vs)) | all (isValue . SimplyExtTerm) vs = return $ vs !! (read i)
    go ctx (Tproj i t) = Tproj i <$> go ctx t
    go ctx (Ttuple vs) = do
      let (a,b:bs) = span (isValue . SimplyExtTerm) vs
      b' <- go ctx b
      return $ Ttuple $ a ++ [b'] ++ bs
    go ctx _ = throwM NoRuleApplies

    subst v p = go where
      go Ttrue = Ttrue
      go Tfalse = Tfalse
      go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
      go (Tsucc t) = Tsucc (go t)
      go (Tpred t) = Tpred (go t)
      go (Tiszero t) = Tiszero (go t)
      go (Tvar y)
        | v == y = p
        | otherwise = Tvar y
      go (Tabs y yt t)
        | v == y = Tabs y yt t
        | otherwise = Tabs y yt (go t)
      go (Tapp t1 t2) = Tapp (go t1) (go t2)
      go Tunit = Tunit
      go (Tas t typ) = Tas (go t) typ
      go (Tlet x t1 t2)
        | x == v = Tlet x t1 t2
        | otherwise = Tlet x (go t1) (go t2)
      go (Tpair t1 t2) = Tpair (go t1) (go t2)
      go (Tpr1 t) = Tpr1 (go t)
      go (Tpr2 t) = Tpr2 (go t)

