{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module SimplyExt where

import Control.Monad
import Data.Tagged
import GHC.TypeLits
import qualified Data.Foldable as F
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Init
import AExp
import Untyped hiding (Var)
import Simply

class (SpType typ) => SpExtType typ where
  baseA :: typ
  unit :: typ

pattern PbaseA = T.Node "A" []
pattern Punit = T.Node "Unit" []

instance SpExtType Syntax where
  baseA = PbaseA
  unit = Punit

--

class (SpExp var typ repr) => SpExtExp var typ repr where
  star :: repr
  (##) :: repr -> repr -> repr
  typeAs :: repr -> typ -> repr

pattern Pstar = T.Node "*" []
pattern Pseq exp1 exp2 = T.Node "##" [exp1, exp2]
pattern PtypeAs exp ty = T.Node "as" [exp, ty]

instance SpExtExp Int Syntax Syntax where
  star = Pstar
  (##) = Pseq
  typeAs = PtypeAs

--

instance SpExtExp Int Syntax (Tagged "typecheck" (Context Syntax -> Syntax)) where
  star = Tagged $ \_ -> unit
  exp1 ## exp2 = Tagged go where
    go ctx =
      let Punit = typeof exp1 ctx in
      typeof exp2 ctx
  typeAs exp ty = Tagged go where
    go ctx =
      case typeof exp ctx of
        z | z == ty -> ty

