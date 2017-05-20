{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module SimplyExt where

import Control.Monad
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

pattern Pstar = T.Node "*" []
pattern Pseq exp1 exp2 = T.Node "##" [exp1, exp2]

instance SpExtExp Int Syntax Syntax where
  star = Pstar
  (##) = Pseq

--

class (Show repr, Show typ, SpExtExp var typ repr, SpExtType typ) => SpExtInfer var typ repr where
  inferSpExt :: Context -> repr -> typ

  typcheckSpExt :: Eq typ => Context -> repr -> typ -> typ
  typcheckSpExt ctx exp typ =
    let te = inferSpExt ctx exp in
    case te == typ of
      True -> typ
      False -> terror exp typ te

instance SpExtInfer Int Syntax Syntax where
  inferSpExt ctx = go where
    go Pstar = unit
    go (Pseq exp1 exp2) =
      let Punit = typcheckSpExt ctx exp1 unit in
      inferSpExt ctx exp2
    go (T.Node "##" es) = error $ show es
    go z = inferSp ctx z
