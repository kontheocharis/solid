-- Defines the syntax for the intermediate representation corresponding to the
-- residual object program produces after the staged program has been evaluated.
module Intermediate.Syntax

import Core.Base

%default total

-- The layout of a type. For now we just use Nat.
public export
Bytes : Type
Bytes = Nat

public export
data ITerm : Ctx -> Type where
  IVar : Idx ns -> ITerm ns
  ILam : (n : Ident) -> (argBytes : Bytes) -> ITerm (ns :< n) -> ITerm ns
  IApp : (lhs, rhs : ITerm ns) -> ITerm ns
  ILet : (n : Ident) -> ITerm ns -> ITerm (ns :< n) -> ITerm ns
  IPair : (fstBytes, sndBytes : Bytes) -> (fst, snd : ITerm ns) -> ITerm ns -- Pair constructor
