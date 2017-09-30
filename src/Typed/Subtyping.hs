module Typed.Subtyping
  ( module Typed.Simply
  , pattern Karr
  , pattern Tval
  , pattern Tvar
  , pattern Tabs
  , pattern Tapp
  , Term(SimplyTerm)
  ) where

import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Tree as T
import Preliminaries
import Typed.Simply
import Typed.SimplyExt (pattern Tfield, pattern Trecord, pattern Kfield, pattern Krecord, pattern Tprojf, lookupKRec, lookupTRec, Term(SimplyExtTerm))

pattern Ktop = Tval "Top"

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  | ExpectedANat
  | WrongKindOfBindingForVariable
  | ParameterTypeMismatch
  | ArrowTypeExpected
  | ExpectedType StrTree StrTree
  | NotFoundLabel String [StrTree]
  deriving Show

instance Exception TypeOfError

subtype :: StrTree -> StrTree -> Bool
subtype = go where
  go tyS tyT | tyS == tyT = True
  go (Trecord fS) (Trecord fT) = all (\(Tfield li tyTi) -> maybe False (\tySi -> go tySi tyTi) (lookupTRec li (Trecord fS))) fT
  go _ Ktop = True
  go (Karr tyS1 tyS2) (Karr tyT1 tyT2) = go tyS1 tyT1 && go tyS2 tyT2
  go _ _ = False

instance Calculus "subtyping" StrTree StrTree (M.Map Var StrTree) where
  data Term "subtyping" StrTree = SubtypeTerm StrTree deriving (Eq, Show)

  isValue (SubtypeTerm t) = go t where
    go (Tabs _ _ _) = True
    go t = isValue (ArithTerm t)

  typeof ctx (SubtypeTerm t) = go ctx t where
    go ctx (Trecord lts) = Krecord <$> mapM (\(Tfield li ti) -> Kfield li <$> go ctx ti) lts
    go ctx (Tprojf l t1) =
      go ctx t1 >>= \case
        Krecord fys -> maybe (throwM $ NotFoundLabel l fys) return $ lookupKRec l (Krecord fys)
        z -> throwM $ ExpectedType (Krecord []) z
    go ctx (Tvar x) = return $ ctx M.! x
    go ctx (Tabs x xt t) = do
      tt <- go (M.insert x xt ctx) t
      return $ Karr xt tt
    go ctx (Tapp tx ty) = do
      txTyp <- go ctx tx
      tyTyp <- go ctx ty
      case txTyp of
        Karr txTyp1 txTyp2 ->
          if subtype tyTyp txTyp1 then return txTyp2
          else throwM ParameterTypeMismatch
        _ -> throwM ArrowTypeExpected

  eval1 (SubtypeTerm t) = (\(SimplyExtTerm t) -> SubtypeTerm t) <$> eval1 (SimplyExtTerm t)
