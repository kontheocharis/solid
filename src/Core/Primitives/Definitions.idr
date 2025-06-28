-- Defining the primitives in the language
module Core.Primitives.Definitions

import Common
import Core.Base
import Decidable.Equality

-- Primitives are either neutral or normal.
--
-- Neutral primitives might still be applied to other arguments after being fully
-- applied to their arity. For example,
--
-- ifThenElse : (A : Type) -> Bool -> A -> A -> A
--
-- is a primitive of arity 4, but could be applied to more than 2 arguments,
-- for example if we instantiate A with a function type:
--
-- Conversely, normal primitives can never be applied to more arguments than their
-- arity.
public export
data PrimitiveClass = PrimNeu | PrimNorm

-- Whether a primitive is reducible or not.
--
-- If it is reducible, it might have some computation rules depending on its arguments.
public export
data PrimitiveReducibility = PrimReducible | PrimIrreducible

-- Whether a primitive is native or declared in the prelude file.
public export
data PrimitiveLevel = PrimNative | PrimDeclared

-- The theory of primitives.
--
-- Consists of a list of operators, each of a specified arity. Equations are
-- given separately later (they are the reduction rules). Will also be given
-- proper types later.
public export
data Primitive : PrimitiveClass -> PrimitiveReducibility -> PrimitiveLevel -> Arity -> Type where
  PrimTYPE : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimCode : Primitive PrimNorm PrimIrreducible PrimNative [(Implicit, "l"), (Explicit, "ty")]
  PrimQuote : Primitive PrimNorm PrimIrreducible PrimNative [(Implicit, "l"), (Implicit, "ty"), (Explicit, "val")]
  PrimSplice : Primitive PrimNorm PrimIrreducible PrimNative [(Implicit, "l"), (Implicit, "ty"), (Explicit, "val")]
  PrimSta : Primitive PrimNorm PrimIrreducible PrimNative [(Explicit, "l")]
  PrimTypeDyn : Primitive PrimNorm PrimIrreducible PrimNative [(Explicit, "l")]
  PrimLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimLayoutDyn : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimSeqLayout : Primitive PrimNorm PrimReducible PrimNative [(Explicit, "a"), (Explicit, "b")]
  PrimSeqLayoutDyn : Primitive PrimNorm PrimReducible PrimNative [(Explicit, "a"), (Explicit, "b")]
  PrimZeroLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimIdxLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimPtrLayout : Primitive PrimNorm PrimIrreducible PrimNative []

-- Can't be DecEq without writing out all cases smh
export
primEq : (a : Primitive k r na ar) -> (b : Primitive k' r' na' ar') -> Maybe (a = b)
primEq PrimTYPE PrimTYPE = Just Refl
primEq PrimCode PrimCode = Just Refl
primEq PrimQuote PrimQuote = Just Refl
primEq PrimSplice PrimSplice = Just Refl
primEq PrimSta PrimSta = Just Refl
primEq PrimTypeDyn PrimTypeDyn = Just Refl
primEq PrimLayout PrimLayout = Just Refl
primEq PrimLayoutDyn PrimLayoutDyn = Just Refl
primEq PrimSeqLayout PrimSeqLayout = Just Refl
primEq PrimSeqLayoutDyn PrimSeqLayoutDyn = Just Refl
primEq PrimZeroLayout PrimZeroLayout = Just Refl
primEq PrimIdxLayout PrimIdxLayout = Just Refl
primEq PrimPtrLayout PrimPtrLayout = Just Refl
primEq _ _ = Nothing

export
primName : Primitive k r na ar -> String
primName PrimTYPE = "TYPE"
primName PrimCode = "Code"
primName PrimQuote = "quote"
primName PrimSplice = "splice"
primName PrimLayout = "Layout"
primName PrimZeroLayout = "zero"
primName PrimIdxLayout = "idx"
primName PrimPtrLayout = "ptr"
primName PrimLayoutDyn = "Layout?"
primName PrimSta = "sta"
primName PrimTypeDyn = "Type?"
primName PrimSeqLayout = "seq"
primName PrimSeqLayoutDyn = "seq-dyn"