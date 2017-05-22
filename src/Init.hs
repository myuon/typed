{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module Init where

import Control.Monad.Catch
import qualified Data.Tree as T
import qualified Data.Map as M
import Data.Tagged
import Data.Typeable
import GHC.TypeLits

type Syntax = T.Tree String

-- contexts

data Binding typ = VarBind typ

instance (Show typ) => Show (Binding typ) where
  show (VarBind t) = show t

type Context a = M.Map Int (Binding a)

(.:) :: (Int, Binding typ) -> M.Map Int (Binding typ) -> M.Map Int (Binding typ)
(x,bind) .: gs = M.insert x bind gs

-- typecheck functions

type Csyn m = Context Syntax -> m Syntax
type Typecheck m = Tagged "typecheck" (Csyn m)

instance Exception (T.Tree String)

class ErrorMsg err where
  should :: String -> String -> err

instance ErrorMsg (T.Tree String) where
  should a b = T.Node "should" [T.Node a [], T.Node b []]

class ErrorMsg err => ErrorMsgContext err where
  notInContext :: String -> Context Syntax -> err
  typeMismatch :: String -> String -> String -> err

throwM' :: (MonadThrow m) => T.Tree String -> m a
throwM' = throwM

terror :: (MonadThrow m) => m Syntax -> String -> String -> m a
terror m exp act = m >>= \m' -> throwM' $ typeMismatch (show m') exp act

typeof :: Context Syntax -> Typecheck m -> m Syntax
typeof ctx m = unTagged m ctx

typeof' = typeof M.empty

typecheck :: (MonadThrow m) => Context Syntax -> Typecheck m -> Syntax -> m Syntax
typecheck ctx exp typ = do
  te <- typeof ctx exp
  case te == typ of
    True -> return typ
    False -> terror (unTagged exp ctx) (show typ) (show te)

-- stored type
type Store a = M.Map String a

type Rsyn m = Context Syntax -> Store Syntax -> m Syntax
type RefTypecheck m = Tagged "reftypecheck" (Rsyn m)

instance ErrorMsgContext (T.Tree String) where
  notInContext v ctx = T.Node "Not in Context" [T.Node v [], T.Node (show ctx) []]
  typeMismatch term exp act = T.Node "TypeMismatch ... Expected: but Actual:" [T.Node term [], T.Node exp [], T.Node act []]

class ErrorMsg err => ErrorMsgStore err where
  notInStore :: String -> Store Syntax -> err

instance ErrorMsgStore (T.Tree String) where
  notInStore v ctx = T.Node "Not in Store" [T.Node v [], T.Node (show ctx) []]

reftypeof :: Context Syntax -> Store Syntax -> RefTypecheck m -> m Syntax
reftypeof ctx sto m = unTagged m ctx sto

reftypeof' = reftypeof M.empty M.empty

reftypecheck :: (MonadThrow m) => Context Syntax -> Store Syntax -> RefTypecheck m -> Syntax -> m Syntax
reftypecheck ctx sto exp typ = do
  te <- reftypeof ctx sto exp
  case te == typ of
    True -> return typ
    False -> terror (unTagged exp ctx sto) (show typ) (show te)

