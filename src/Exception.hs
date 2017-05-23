{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Exception where

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

class (SpExp var typ repr) => ExcExp var typ repr where
  err :: typ -> repr
  try_with :: repr -> repr -> repr
  raise :: repr -> typ -> repr

pattern Perr t = T.Node "error_as" [t]
pattern Ptry t1 t2 = T.Node "try with" [t1,t2]
pattern Praise t1 t2 = T.Node "raise_as" [t1,t2]

instance ExcExp Int Syntax Syntax where
  err = Perr
  try_with = Ptry
  raise = Praise

-- nat as exception type
instance MonadThrow m => ExcExp Int Syntax (ContextOf m) where
  err ty = Tagged $ \_ -> return ty
  try_with t1 t2 = Tagged go where
    go ctx = do
      ty1 <- typeof @"context" ctx t1
      typeof @"context" ctx t2 >>=
        \case
          Parrow Pnat ty' | ty' == ty1 -> return ty'
          z -> terror (unTagged t2 ctx) (show $ Parrow Pnat wild) (show z)
  raise t1 t2 = Tagged go where
    go ctx = seq (typecheck @"context" ctx t1 nat) $ return t2


