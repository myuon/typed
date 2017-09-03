module Typed.Arith where

import Control.Monad.Catch
import Untyped.Arith
import Preliminaries

pattern Tbool = Node "bool" []

data TypeOfError
  = ArmsOfConditionalHasDifferentTypes
  | GuardOfConditionalNotABoolean
  deriving Show
instance Exception TypeOfError

instance Calculus "typed.arith" StrTree StrTree () where
  newtype Term "typed.arith" StrTree = ArithTerm StrTree

  isValueR rec' (ArithTerm t) = go t where
    go Ttrue = True
    go Tfalse = True
    go _ = False

  typeofR rec' ctx (ArithTerm t) = go ctx t where
    rec ctx = rec' ctx . ArithTerm
    
    go ctx Ttrue = return Tbool
    go ctx Tfalse = return Tbool
    go ctx (Tif t a b) = do
      tt <- rec ctx t
      if tt == Tbool
        then do
        ta <- rec ctx a
        tb <- rec ctx b
        if ta == tb then return ta else throwM ArmsOfConditionalHasDifferentTypes
        else throwM GuardOfConditionalNotABoolean


