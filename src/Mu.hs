{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
module Mu where

import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Control.Monad.State
import Control.Arrow (second, (***))
import Control.Lens hiding (Context)

newtype VarId = VarId String deriving (Eq, Ord)
newtype CtrlId = CtrlId String deriving (Eq, Ord)
newtype HoleId = HoleId Int deriving (Eq, Ord)

instance Show VarId where show (VarId v) = v
instance Show CtrlId where show (CtrlId v) = v
instance Show HoleId where show (HoleId v) = show v

data Expr =
  Var VarId
  | Lambda VarId Expr
  | App Expr Expr
  | Name CtrlId Expr
  | Mu CtrlId Expr
  deriving (Eq)

var :: String -> Expr
var = Var . VarId

lam :: String -> Expr -> Expr
lam v = Lambda (VarId v)

infixl 2 <#>
(<#>) :: Expr -> Expr -> Expr
(<#>) e1 e2 = App e1 e2

name :: String -> Expr -> Expr
name v = Name (CtrlId v)

mu :: String -> Expr -> Expr
mu v = Mu (CtrlId v)

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
  show (Name c expr) = "[" ++ show c ++ "] " ++ show expr
  show (Mu c expr) = "μ" ++ show c ++ ". " ++ show expr

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
  _cctx :: Context CtrlId,
  _unifiers :: Unifiers
  }
  deriving (Eq, Show)

makeLenses ''Environment

defEnv :: Environment
defEnv = Environment (HoleId 0) M.empty M.empty S.empty

newHole :: State Environment HoleId
newHole = do
  hole <- use holeIndex
  holeIndex %= (\(HoleId n) -> HoleId $ n+1)
  return hole

typeCheck :: Expr -> Either String Typ
typeCheck expr = reindex <$> evalState (typing expr) defEnv
  where
    reindex t = go t where
      rmap = zip (holesIn t) (fmap hole [0..])

      go (Hole v) = fromJust $ lookup v rmap
      go (Arrow e1 e2) = Arrow (go e1) (go e2)
      go Bottom = Bottom

typing :: Expr -> State Environment (Either String Typ)
typing (Var var) = do
  vmap <- use vctx
  case var `M.member` vmap of
    True -> return $ Right $ vmap M.! var
    False -> return $ Left $ "Variable not in scope: " ++ show var ++ " in " ++ show vmap
typing (Lambda var expr) = do
  vmap <- use vctx
  mtyp <- case var `M.member` vmap of
    True -> return $ Left $ "Variable already used: " ++ show var ++ " in " ++ show vmap
    False -> do
      newHole >>= \hole -> vctx %= M.insert var (Hole hole)
      typing expr
  vmap <- use vctx
  return $ (\m -> (vmap M.! var) ~> m) <$> mtyp
typing (App expr1 expr2) = do
  typ1 <- typing expr1
  typ2 <- typing expr2
  case (typ1, typ2) of
    (Left e1, Left e2) -> return $ Left $ e1 ++ "\n" ++ e2
    (Left e, _) -> return $ Left e
    (_, Left e) -> return $ Left e
    (Right t1, Right t2) -> do
      vctx %= M.insert (VarId "?goal") t1
      succeeded <- do
        h <- newHole
        us <- use unifiers
        unify (S.insert (t1, t2 ~> Hole h) us)

      case succeeded of
        Left err -> return $ Left err
        Right us -> do
          unifiers .= us

          use vctx >>= \vmap -> case vmap M.! VarId "?goal" of
            (Arrow _ v) -> return $ Right v
            t -> return $ Left $ "Type not match: " ++ show t ++ " is not a function type"
typing (Name name expr) = do
  etyp <- typing expr
  cmap <- use cctx

  case etyp of
    Left err -> return $ Left err
    _ | name `M.notMember` cmap -> return $ Left $ "Name not in scope: " ++ show name ++ " in " ++ show cmap
    Right typ -> do
      -- Appの推論では?goalを付け加えたがここでは
      -- nameの型は後で使わないので不要
      succeeded <- do
        cmap <- use cctx
        us <- use unifiers
        unify $ S.insert (typ, cmap M.! name) us

      case succeeded of
        Left err -> return $ Left err
        Right us -> do
          unifiers .= us
          return $ Right Bottom
typing (Mu name expr) = do
  cmap <- use cctx
  case name `M.member` cmap of
    True -> return $ Left $ "Name already used: " ++ show name ++ " in " ++ show cmap
    False -> do
      newHole >>= \h -> cctx %= M.insert name (Hole h)
      etyp <- typing expr

      case etyp of
        Left err -> return $ Left err
        Right typ -> do
          succeeded <- do
            cmap <- use cctx
            us <- use unifiers
            unify $ S.insert (typ, Bottom) us

          case succeeded of
            Left err -> return $ Left err
            Right us -> do
              unifiers .= us
              us' <- use unifiers
              cmap <- use cctx
              return $ Right $ cmap M.! name

holesIn :: Typ -> [HoleId]
holesIn = nub . go where
  go Bottom = []
  go (Arrow t1 t2) = go t1 ++ go t2
  go (Hole v) = [v]

unify :: Unifiers -> State Environment (Either String Unifiers)
unify us = case S.minView us of
  Just (this, others) -> go this others
  Nothing -> return $ Right S.empty
  where
    subst :: HoleId -> Typ -> Typ -> Typ
    subst v m (Hole w)
      | v == w = m
      | otherwise = Hole w
    subst v m (Arrow t1 t2) = Arrow (subst v m t1) (subst v m t2)
    subst v m Bottom = Bottom

    go this others = case this of
      (p, q) | p == q -> unify others
      (Arrow t11 t12, Arrow t21 t22) -> unify $ S.insert (t11,t21) $ S.insert (t21,t22) others
      (p@(Arrow _ _), Hole v) -> unify $ S.insert (Hole v, p) others
      (Hole v, typ)
        | v `elem` holesIn typ -> return $ Left $ "Unification failed (loop): " ++ show (Hole v) ++ " in " ++ show typ
        | otherwise -> do
          vctx %= fmap (subst v typ)
          cctx %= fmap (subst v typ)
          es <- unify $ S.map (subst v typ *** subst v typ) others
          return $ S.insert (Hole v, typ) <$> es
      (p,q) -> return $ Left $ "Unification failed: " ++ show p ++ " & " ++ show q

normalize :: Expr -> Expr
normalize = go where
  substV :: Expr -> VarId -> Expr -> Expr
  substV (Var w) v m
    | v == w = m
    | otherwise = Var w
  substV (Lambda x t) v m = Lambda x (substV t v m)
  substV (App t1 t2) v m = App (substV t1 v m) (substV t2 v m)
  substV (Name c t) v m = Name c (substV t v m)
  substV (Mu a t) v m = Mu a (substV t v m)

  substC :: Expr -> CtrlId -> Expr -> Expr
  substC (Name beta w) alpha m
    | beta == alpha = Name beta (App (substC w alpha m) m)
    | otherwise = Name beta (substC w alpha m)
  substC (Var x) alpha m = Var x
  substC (Lambda x t) alpha m = Lambda x $ substC t alpha m
  substC (App t1 t2) alpha m = App (substC t1 alpha m) (substC t2 alpha m)
  substC (Mu beta t) alpha m = Mu beta (substC t alpha m)

  go (App (Lambda var u) v) = go $ substV u var v
  go (App (Mu alpha u) v) = go $ Mu alpha $ substC u alpha v
  go (Var x) = Var x
  go (Lambda var m) = Lambda var $ go m
  go (App t1 t2) = App (go t1) (go t2)
  go (Name alpha m) = Name alpha $ go m
  go (Mu alpha m) = Mu alpha $ go m

run = do
  let expr = (Lambda (VarId "f") $ Mu (CtrlId "a") $ App (var "f") (Lambda (VarId "x") $ Name (CtrlId "a") $ var "x"))
  print $ typeCheck expr
  print $ runState (typing expr) defEnv
