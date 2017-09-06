module Typed.SimplyExt
  ( module Typed.Simply
  , pattern Kbase
  , pattern Tunit, pattern Kunit, pattern (:.)
  , pattern Tas
  , pattern Tlet
  , pattern Tpair, pattern Tpr1, pattern Tpr2, pattern Kpair
  , pattern Ttuple, pattern Tproj, pattern Ktuple
  , pattern Tfield, pattern Trecord, pattern Kfield, pattern Krecord, pattern Tprojf
  , pattern Tinlas, pattern Tinras, pattern Tcase, pattern Ksum
  , pattern Ttagged, pattern Tmatch, pattern Tcasev, pattern Ktagged, pattern Kvariant
  , pattern Tfix, pattern Tletrec
  , pattern Tnil, pattern Tcons, pattern Tisnil, pattern Thead, pattern Ttail, pattern Klist
  , Term(SimplyExtTerm)
  ) where

import Control.Monad
import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import qualified Data.Text.Lazy as Text
import Data.Text.Format
import Data.String (fromString)
import Data.List
import Preliminaries
import Typed.Simply

pattern Kbase = T.Node "A" []

pattern Kunit = T.Node "Unit" []
pattern Tunit = T.Node "unit" []
pattern (:.) tx ty <- (Tabs "*" Kunit ty) `Tapp` tx

pattern Tas t typ = T.Node "as" [t,typ]

pattern Tlet x t1 t2 = T.Node "let {} = {} in {}" [Tval x,t1,t2]

pattern Tpair x y = T.Node "{{},{}}" [x,y]
pattern Tpr1 x = T.Node "{}.1" [x]
pattern Tpr2 x = T.Node "{}.2" [x]
pattern Kpair x y = T.Node "({},{})" [x,y]

pattern Ttuple xs = T.Node "{{}}" xs
pattern Tproj i t = T.Node "{}.at({})" [t,Tval i]
pattern Ktuple xs = T.Node "({})" xs

pattern Tfield l t = T.Node "{} := {}" [Tval l,t]
pattern Trecord lts = T.Node "record" lts
pattern Kfield l t = T.Node "{} : {}" [Tval l,t]
pattern Krecord lts = T.Node "record type" lts
pattern Tprojf l t = T.Node "{}.label({})" [t,Tval l]

pattern Tinlas t typ = T.Node "inl {} as {}" [t,typ]
pattern Tinras t typ = T.Node "inr {} as {}" [t,typ]
pattern Tcase t t1 t2 = T.Node "case {} of inl => {} | inr => {}" [t,t1,t2]
pattern Ksum x y = T.Node "{} + {}" [x,y]

pattern Ttagged l t typ = T.Node "<{} := {}> as {}" [Tval l,t,typ]
pattern Tmatch l x t = T.Node "<{} = {}> -> {}" [Tval l,Tval x,t]
pattern Pcase xs = T.Node "case" xs
pattern Tcasev t hs = T.Node "case {} of {}" [t, Pcase hs]
pattern Ktagged l typ = T.Node "{} : {}" [Tval l,typ]
pattern Kvariant xs = T.Node "variant" xs

pattern Tfix t = T.Node "fix {}" [t]
pattern Tletrec x typ t1 t2 <- Tlet x (Tfix (Tabs x typ t1)) t2

pattern Tnil typ = T.Node "nil[{}]" [typ]
pattern Tcons typ t1 t2 = T.Node "cons[{}] {} {}" [typ,t1,t2]
pattern Tisnil typ t = T.Node "isnil[{}] {}" [typ,t]
pattern Thead typ t = T.Node "head[{}] {}" [typ,t]
pattern Ttail typ t = T.Node "tail[{}] {}" [typ,t]
pattern Klist typ = T.Node "List {}" [typ]

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | ExpectedANat
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  | ExpectedType StrTree StrTree
  | NotFound String
  | CaseMatchNotHaveSameType [StrTree]
  deriving Show

instance Exception TypeOfError

instance Show (Term "simply-ext" StrTree) where
  show (SimplyExtTerm t) = go t where
    go (Krecord lts) = Text.unpack $ format (fromString $ (\y -> "{" ++ y ++ "}") $ intercalate "," $ replicate (length lts) "{}") (fmap go lts)
    go (Trecord lts) = Text.unpack $ format (fromString $ (\y -> "{" ++ y ++ "}") $ intercalate ", " $ replicate (length lts) "{}") (fmap go lts)
    go (T.Node l xs) = Text.unpack $ format (fromString l) (fmap go xs)

instance Calculus "simply-ext" StrTree StrTree (M.Map Var Binding) where
  newtype Term "simply-ext" StrTree = SimplyExtTerm StrTree deriving (Eq)

  isValue (SimplyExtTerm t) = go t where
    go Tunit = True
    go (Tpair t1 t2) = go t1 && go t2
    go (Ttuple ts) = all (isValue . SimplyExtTerm) ts
    go (Tinlas v _) = go v
    go (Tinras v _) = go v
    go (Tnil _) = True
    go (Tcons _ v1 v2) = go v1 && go v2
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
        z -> throwM $ ExpectedType Kbool z
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
        Knat -> return Kbool
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
    go ctx (Trecord lts) = do
      tsT <- mapM (\(Tfield l t) -> Kfield l <$> go ctx t) lts
      return $ Krecord tsT
    go ctx (Tprojf l t) = do
      tT <- go ctx t
      case tT of
        Krecord tTs -> return $ (\(Kfield u t) -> t) $ head $ filter (\(Kfield u t) -> l == u) tTs
        z -> throwM $ ExpectedType (Krecord [Kfield l (Tval "_")]) z
    go ctx (Tinlas t typ) = do
      case typ of
        Ksum typT1 typT2 -> do
          tT <- go ctx t
          if tT == typT1 then return typ else throwM $ ExpectedType typT1 tT
        _ -> throwM $ ExpectedType (Ksum (Tval "_") (Tval "_")) typ
    go ctx (Tinras t typ) = do
      case typ of
        Ksum typT1 typT2 -> do
          tT <- go ctx t
          if tT == typT2 then return typ else throwM $ ExpectedType typT2 tT
        _ -> throwM $ ExpectedType (Ksum (Tval "_") (Tval "_")) typ
    go ctx (Ttagged l t typ) = do
      tT <- go ctx t
      case typ of
        Kvariant xs | (l,tT) `elem` fmap (\(Ktagged l t) -> (l,t)) xs -> return $ typ
        z -> throwM $ ExpectedType typ (Kvariant [Ktagged l tT])
    go ctx (Tcasev t lxt) = do
      tT <- go ctx t
      case tT of
        Kvariant lts | sort (fmap (\(Tmatch l _ _) -> l) lxt) == sort (fmap (\(Ktagged l _) -> l) lts) -> do
          ts <- forM lxt $ \(Tmatch li xi ti) -> do
            tTi <- lookup' li lts
            go (M.insert xi (VarBind tTi) ctx) ti
          if length (nub ts) <= 1
            then return $ head ts
            else throwM $ CaseMatchNotHaveSameType ts
        z -> throwM $ ExpectedType (Kvariant [Tval "_"]) z

      where
        lookup' :: MonadThrow m => String -> [StrTree] -> m StrTree
        lookup' l [] = throwM $ NotFound l
        lookup' l (Ktagged l' typ : ks)
          | l == l' = return typ
          | otherwise = lookup' l ks
    go ctx (Tfix t) = do
      tT <- go ctx t
      case tT of
        Karr tT1 tT2 | tT1 == tT2 -> return tT1
        z -> throwM $ ExpectedType (Karr (Tval "?a") (Tval "?a")) z
    go ctx (Tnil typ) = return $ Klist typ
    go ctx (Tcons typ t1 t2) = do
      t1T <- go ctx t1
      t2T <- go ctx t2
      if t1T == typ && t2T == Klist typ
        then return $ Klist typ
        else throwM $ ExpectedType (Klist typ) (T.Node "{} or {}" [t1T,t2T])
    go ctx (Tisnil typ t) = do
      tT <- go ctx t
      case tT of
        Klist tT' | tT' == typ -> return Kbool
        z -> throwM $ ExpectedType (Klist typ) z
    go ctx (Thead typ t) = do
      tT <- go ctx t
      case tT of
        Klist tT' | tT' == typ -> return $ typ
        z -> throwM $ ExpectedType (Klist typ) z
    go ctx (Ttail typ t) = do
      tT <- go ctx t
      case tT of
        Klist tT' | tT' == typ -> return $ Klist typ
        z -> throwM $ ExpectedType (Klist typ) z

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
    go ctx (Tprojf l (Trecord lts))
      | all (\(Tfield l t) -> isValue (SimplyExtTerm t)) lts = return $ (\(Tfield u t) -> t) $ head $ filter (\(Tfield u t) -> l == u) lts
      | otherwise = Tprojf l <$> go ctx (Trecord lts)
    go ctx (Trecord vs) = do
      let (a,Tfield lb b:bs) = span (\(Tfield l v) -> isValue (SimplyExtTerm v)) vs
      b' <- go ctx b
      return $ Trecord $ a ++ [Tfield lb b'] ++ bs
    go ctx (Tcase (Tinlas v vT) t1 t2) | isValue (SimplyExtTerm v) = go ctx $ t1 `Tapp` v
    go ctx (Tcase (Tinras v vT) t1 t2) | isValue (SimplyExtTerm v) = go ctx $ t2 `Tapp` v
    go ctx (Tcase t t1 t2) = Tcase <$> go ctx t <*> return t1 <*> return t2
    go ctx (Tinlas v vT) = Tinlas <$> go ctx v <*> return vT
    go ctx (Tinras v vT) = Tinras <$> go ctx v <*> return vT
    go ctx (Tcasev (Ttagged l v typ) lxt) | isValue (SimplyExtTerm v) = do
      Tmatch l x t <- lookup' l lxt
      return $ subst x v t
      where
        lookup' :: MonadThrow m => String -> [StrTree] -> m StrTree
        lookup' l [] = throwM $ NotFound l
        lookup' l (Tmatch l' x t : ks)
          | l == l' = return $ Tmatch l' x t
          | otherwise = lookup' l ks
    go ctx (Tcasev t lxt) = Tcasev <$> go ctx t <*> return lxt
    go ctx (Ttagged l t typ) = Ttagged l <$> go ctx t <*> return typ
    go ctx (Tfix (Tabs x typ t)) = return $ subst x (Tfix (Tabs x typ t)) t
    go ctx (Tfix t) = Tfix <$> go ctx t
    go ctx (Tcons typ t1 t2)
      | isValue (SimplyExtTerm t1) = Tcons typ t1 <$> go ctx t2
      | otherwise = Tcons typ <$> go ctx t1 <*> return t2
    go ctx (Tisnil typ (Tnil _)) = return Ttrue
    go ctx (Tisnil typ (Tcons _ _ _)) = return Tfalse
    go ctx (Tisnil typ t) = Tisnil typ <$> go ctx t
    go ctx (Thead typ (Tcons _ v1 v2)) | isValue (SimplyExtTerm v1) && isValue (SimplyExtTerm v2) = return v1
    go ctx (Thead typ t) = Thead typ <$> go ctx t
    go ctx (Ttail typ (Tcons _ v1 v2)) | isValue (SimplyExtTerm v1) && isValue (SimplyExtTerm v2) = return v2
    go ctx (Ttail typ t) = Ttail typ <$> go ctx t
    go ctx _ = throwM NoRuleApplies

    subst v p = go where
      go Ttrue = Ttrue
      go Tfalse = Tfalse
      go (Tif b t1 t2) = Tif (go b) (go t1) (go t2)
      go Tzero = Tzero
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
      go (Tproj i t) = Tproj i (go t)
      go (Ttuple vs) = Ttuple (fmap go vs)
      go (Trecord rs) = Trecord (fmap go rs)
      go (Tprojf l t) = Tprojf l (go t)
      go (Tcase t t1 t2) = Tcase (go t) (go t1) (go t2)
      go (Tinlas t tT) = Tinlas (go t) tT
      go (Tinras t tT) = Tinras (go t) tT
      go (Tcasev t lxt) = Tcasev (go t) (fmap (\(Tmatch l x t) -> Tmatch l x (go t)) lxt)
      go (Tfix t) = Tfix (go t)

