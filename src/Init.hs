{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module Init where

import Control.Monad.Catch
import qualified Data.Tree as T
import qualified Data.Map as M
import Data.Tagged
import GHC.TypeLits

type Syntax = T.Tree String

-- typecheck functions

instance Exception (T.Tree String)

class ErrorMsg err where
  should :: String -> String -> err

instance ErrorMsg (T.Tree String) where
  should a b = T.Node "should" [T.Node a [], T.Node b []]

class TypeOf (sym :: Symbol) where
  type K (sym :: Symbol) (a :: *) :: *
  typeof :: K sym (Tagged sym (K sym (m Syntax)) -> m Syntax)
  typeof' :: Tagged sym (K sym (m Syntax)) -> m Syntax

  typecheck :: (MonadThrow m) => K sym (Tagged sym (K sym (m Syntax)) -> Syntax -> m Syntax)

-- evaluation

type CBV = Tagged "cbv" Syntax

-- contexts

data Binding typ = VarBind typ

instance (Show typ) => Show (Binding typ) where
  show (VarBind t) = show t

type Context a = M.Map Int (Binding a)

(.:) :: (Int, Binding typ) -> M.Map Int (Binding typ) -> M.Map Int (Binding typ)
(x,bind) .: gs = M.insert x bind gs

class ErrorMsg err => ErrorMsgContext err where
  notInContext :: String -> Context Syntax -> err
  typeMismatch :: String -> String -> String -> err

instance ErrorMsgContext (T.Tree String) where
  notInContext v ctx = T.Node "Not in Context" [T.Node v [], T.Node (show ctx) []]
  typeMismatch term exp act = T.Node "TypeMismatch ... Expected: but Actual:" [T.Node term [], T.Node exp [], T.Node act []]

throwM' :: (MonadThrow m) => T.Tree String -> m a
throwM' = throwM

terror :: (MonadThrow m) => m Syntax -> String -> String -> m a
terror m exp act = m >>= \m' -> throwM' $ typeMismatch (show m') exp act

instance TypeOf "context" where
  type K "context" a = Context Syntax -> a
  typeof ctx m = unTagged m ctx
  typeof' = typeof @"context" M.empty

  typecheck ctx exp typ = do
    te <- typeof @"context" ctx exp
    case te == typ of
      True -> return typ
      False -> terror (unTagged exp ctx) (show typ) (show te)

type ContextOf m = Tagged "context" (Context Syntax -> m Syntax)

-- context, subtyping

class ErrorMsgContext err => ErrorMsgSubtype err where
  notInRecord :: String -> Syntax -> err

instance ErrorMsgSubtype (T.Tree String) where
  notInRecord label es = T.Node "Not in Record" [T.Node label [], T.Node (show es) []]

instance TypeOf "subcontext" where
  type K "subcontext" a = Context Syntax -> a
  typeof ctx m = unTagged m ctx
  typeof' = typeof @"subcontext" M.empty

  typecheck ctx exp typ = do
    te <- typeof @"subcontext" ctx exp
    case te == typ of
      True -> return typ
      False -> terror (unTagged exp ctx) (show typ) (show te)

type SubContextOf m = Tagged "subcontext" (Context Syntax -> m Syntax)

-- store

type Store a = M.Map String a

class ErrorMsg err => ErrorMsgStore err where
  notInStore :: String -> Store Syntax -> err

instance ErrorMsgStore (T.Tree String) where
  notInStore v ctx = T.Node "Not in Store" [T.Node v [], T.Node (show ctx) []]

instance TypeOf "store" where
  type K "store" a = Context Syntax -> Store Syntax -> a
  typeof ctx sto m = unTagged m ctx sto
  typeof' = typeof @"store" M.empty M.empty

  typecheck ctx sto exp typ = do
    te <- typeof @"store" ctx sto exp
    case te == typ of
      True -> return typ
      False -> terror (unTagged exp ctx sto) (show typ) (show te)

type StoreOf m = Tagged "store" (Context Syntax -> Store Syntax -> m Syntax)

