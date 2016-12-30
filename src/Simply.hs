{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
module Simply where

import Data.Typeable
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Catch
import Control.Arrow (second, (***))
import Control.Lens hiding (Context)

data VarId = VarId String Int deriving (Eq, Ord)
newtype HoleId = HoleId Int deriving (Eq, Ord)

instance Show VarId where show (VarId v uid) = v
instance Show HoleId where show (HoleId v) = show v

data Expr =
  Var VarId
  | Lambda VarId Expr
  | App Expr Expr
  deriving (Eq)

varId :: String -> VarId
varId s = VarId s 0

var :: String -> Expr
var = Var . varId

lam :: String -> Expr -> Expr
lam v = Lambda (varId v)

infixl 2 <#>
(<#>) :: Expr -> Expr -> Expr
(<#>) = App

instance Show Expr where
  show (Var v) = show v
  show (Lambda v expr) = "λ" ++ show v ++ ". " ++ show expr
  show (App e1 e2) = case (e1,e2) of
    (App _ _, Var _) -> show e1 ++ show e2
    (Var _, Var _) -> show e1 ++ show e2
    (_, Var _) -> "(" ++ show e1 ++ ")" ++ show e2
    (App _ _, _) -> show e1 ++ "(" ++ show e2 ++ ")"
    (Var _, _) -> show e1 ++ "(" ++ show e2 ++ ")"
    (_,_) -> "(" ++ show e1 ++ ")(" ++ show e2 ++ ")"

data Typ =
  Arrow Typ Typ
  | Bottom
  | Hole HoleId
  deriving (Eq, Ord)

instance Show Typ where
  show (Arrow t1@(Arrow _ _) t2) = "(" ++ show t1 ++ ") -> " ++ show t2
  show (Arrow t1 t2) = show t1 ++ " -> " ++ show t2
  show Bottom = "_|_"
  show (Hole v) = "?" ++ show v

infixr 5 ~>

(~>) :: Typ -> Typ -> Typ
(~>) = Arrow

hole :: Int -> Typ
hole = Hole . HoleId

type Unifiers = S.Set (Typ, Typ)
type Context k = M.Map k Typ

data Environment = Environment {
  _holeIndex :: HoleId,
  _vctx :: Context VarId,
  _unifiers :: Unifiers
  }
  deriving (Eq, Show)

makeLenses ''Environment

def :: Environment
def = Environment (HoleId 0) M.empty S.empty

newHole :: (Monad m) => StateT Environment m HoleId
newHole = do
  hole <- use holeIndex
  holeIndex %= (\(HoleId n) -> HoleId $ n+1)
  return hole

shadowing :: Expr -> Expr
shadowing expr = evalState (rename expr) 0
  where
    renameVar v0 uid = go where
      go (Var (VarId v _)) | v0 == v = Var (VarId v uid)
      go (Var v) = Var v
      go (Lambda v expr) = Lambda v (go expr)
      go (App e1 e2) = App (go e1) (go e2)

    rename :: Expr -> State Int Expr
    rename (Var v) = return $ Var v
    rename (Lambda (VarId v _) expr) = do
      uid <- get
      modify (+1)
      expr' <- rename $ renameVar v uid expr
      return $ Lambda (VarId v uid) expr'
    rename (App e1 e2) = liftM2 App (rename e1) (rename e2)

unshadowing :: Expr -> Expr
unshadowing = go where
  go (Var (VarId v _)) = Var (varId v)
  go (Lambda (VarId v _) expr) = Lambda (varId v) (go expr)
  go (App e1 e2) = App (go e1) (go e2)

data TypeError = VariableNotInScope String | VariableAlreadyUsed String | TypeNotMatch String
  deriving (Show, Typeable)

instance Exception TypeError

typing :: MonadThrow m => Expr -> m Typ
typing expr = reindex <$> evalStateT (typing' $ shadowing expr) def
  where
    reindex t = go t where
      rmap = zip (holesIn t) (fmap hole [0..])

      go (Hole v) = fromJust $ lookup v rmap
      go (Arrow e1 e2) = Arrow (go e1) (go e2)
      go Bottom = Bottom

    typing' :: MonadThrow m => Expr -> StateT Environment m Typ
    typing' (Var var) = do
      vmap <- use vctx
      case var `M.member` vmap of
        True -> return $ vmap M.! var
        False -> throwM $ VariableNotInScope $ "Variable not in scope: " ++ show var ++ " in " ++ show vmap
    typing' (Lambda var expr) = do
      vmap <- use vctx
      mtyp <- case var `M.member` vmap of
        True -> throwM $ VariableAlreadyUsed $ "Variable already used: " ++ show var ++ " in " ++ show vmap
        False -> do
          h <- newHole
          vctx %= M.insert var (Hole h)
          typing' expr
      vmap <- use vctx
      return $ (vmap M.! var) ~> mtyp
    typing' (App expr1 expr2) = do
      env <- get
      typ1 <- typing' expr1
      vctx %= M.filterWithKey (\k _ -> k `M.member` (env^.vctx))
      typ2 <- typing' expr2
      vctx %= M.filterWithKey (\k _ -> k `M.member` (env^.vctx))

      (us,typ) <- join $ liftM2 (\h -> unify (typ1, typ2 ~> Hole h)) newHole (use unifiers)
      unifiers .= us
      case typ of
        (Arrow _ v) -> return v
        t -> throwM $ TypeNotMatch $ "Type not match: " ++ show t ++ " is not a function type"

typeCheck :: MonadThrow m => Expr -> Typ -> m Typ
typeCheck expr typ = do
  let hs = holesIn typ
  let HoleId m = if null hs then HoleId 0 else maximum hs
  typ' <- typing expr
  snd <$> evalStateT (unify (typ, hmap (\(HoleId h) -> HoleId (h+m+1)) typ') S.empty) def

  where
    hmap :: (HoleId -> HoleId) -> Typ -> Typ
    hmap f = go where
      go (Hole n) = Hole $ f n
      go (Arrow e1 e2) = Arrow (go e1) (go e2)
      go Bottom = Bottom

holesIn :: Typ -> [HoleId]
holesIn = nub . go where
  go Bottom = []
  go (Arrow t1 t2) = go t1 ++ go t2
  go (Hole v) = [v]

data UnificationError = UnificationFailed String | UnificationLoop String
  deriving (Show, Typeable)

instance Exception UnificationError

unify :: MonadThrow m => (Typ, Typ) -> Unifiers -> StateT Environment m (Unifiers, Typ)
unify pq us = do
  vctx %= M.insert (varId "?goal") (pq ^. _1)
  r <- unify' $ S.insert pq us
  vmap <- use vctx
  vctx %= M.delete (varId "?goal")

  return (r, vmap M.! varId "?goal")
  where
    subst :: HoleId -> Typ -> Typ -> Typ
    subst v m (Hole w)
      | v == w = m
      | otherwise = Hole w
    subst v m (Arrow t1 t2) = Arrow (subst v m t1) (subst v m t2)
    subst v m Bottom = Bottom

    unify' :: MonadThrow m => Unifiers -> StateT Environment m Unifiers
    unify' us = case S.minView us of
      Just j -> uncurry go j
      Nothing -> return S.empty

    go :: MonadThrow m => (Typ, Typ) -> Unifiers -> StateT Environment m Unifiers
    go this others = case this of
      (p,q) | p == q -> unify' others
      (Arrow t11 t12, Arrow t21 t22) -> unify' $ S.insert (t11,t21) $ S.insert (t12,t22) others
      (p@(Arrow _ _), Hole v) -> go (Hole v, p) others
      (Bottom, Hole v) -> go (Hole v, Bottom) others
      (Hole v, Hole v') | v > v' -> go (Hole v', Hole v) others
      (Hole v, typ)
        | v `elem` holesIn typ -> throwM $ UnificationLoop $ "Unification failed (loop): " ++ show (Hole v) ++ " in " ++ show typ
        | otherwise -> do
          vctx %= fmap (subst v typ)
          es <- unify' $ S.map (subst v typ *** subst v typ) others
          return $ S.insert (Hole v, typ) es
      (p,q) -> throwM $ UnificationFailed $ "Unification failed: " ++ show p ++ " & " ++ show q

normalize :: Expr -> Expr
normalize = unshadowing . go . shadowing where
  substV :: Expr -> VarId -> Expr -> Expr
  substV (Var w) v m
    | v == w = m
    | otherwise = Var w
  substV (Lambda x t) v m = Lambda x (substV t v m)
  substV (App t1 t2) v m = App (substV t1 v m) (substV t2 v m)

  go (App (Lambda var u) v) = go $ substV u var v
  go (Var x) = Var x
  go (Lambda var m) = Lambda var $ go m
  go (App t1 t2) = let t1' = go t1; t2' = go t2 in
    (if t1 == t1' && t2 == t2' then id else go) $ App t1' t2'

main :: IO ()
main = return ()
