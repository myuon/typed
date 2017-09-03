{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
module Preliminaries where

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Functor.Foldable
import Data.Functor.Classes
import Data.Function (fix)
import Data.Proxy
import GHC.TypeLits

class Calculus (c :: Symbol) trm typ ctx | c -> trm typ ctx where
  data Term c trm
  isValueR :: (Term c trm -> Bool) -> Term c trm -> Bool
  typeofR :: MonadThrow m => (ctx -> Term c trm -> m typ) -> ctx -> Term c trm -> m typ
  evalR :: MonadThrow m => (ctx -> Term c trm -> m (Term c trm)) -> (ctx -> Term c trm -> m (Term c trm))

isValue :: (Calculus c trm typ ctx) => Term c trm -> Bool
isValue = fix isValueR

eval :: (Calculus c trm typ ctx, MonadCatch m) => ctx -> Term c trm -> m (Term c trm)
eval ctx t = let eval1 = fix evalR in catch (eval1 ctx t >>= eval ctx) $ \case
  NoRuleApplies -> return t

typeof :: (Calculus c trm typ ctx, MonadThrow m) => ctx -> Term c trm -> m typ
typeof = fix typeofR

data TreeF a r = NodeF a [r] deriving (Functor, Eq, Show)
type StrTreeF = TreeF String
type Tree a = Fix (TreeF a)
type StrTree = Tree String

instance Show1 (TreeF String) where
  liftShowsPrec sp sl d (NodeF a rs) = showParen (d > 10) $
    showString "NodeF" . showChar ' ' . showString a . showChar ' ' . foldl (\sws a -> sws . sp 11 a) id rs

instance Eq1 (TreeF String) where
  liftEq f (NodeF a r) (NodeF b r') = a == b && length r == length r' && all (uncurry f) (zip r r')

pattern Node a r = Fix (NodeF a r)

data EvalError = NoRuleApplies deriving Show
instance Exception EvalError

