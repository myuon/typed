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

data ErrorMsg
  = NotInContext String (Context Syntax)
  | TypeMismatch String String String
  | Should String String
  deriving (Show, Typeable)

instance Exception ErrorMsg

terror :: (MonadThrow m) => m Syntax -> String -> String -> m a
terror m exp act = m >>= \m' -> throwM $ TypeMismatch (show m') exp act

typeof :: Context Syntax -> Typecheck m -> m Syntax
typeof ctx m = unTagged m ctx

typecheck :: (MonadThrow m) => Context Syntax -> Typecheck m -> Syntax -> m Syntax
typecheck ctx exp typ = do
  te <- typeof ctx exp
  case te == typ of
    True -> return typ
    False -> terror (unTagged exp ctx) (show typ) (show te)

