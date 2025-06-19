-- Defining the primitives in the language
module Core.Primitives

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

-- The theory of primitives.
--
-- Consists of a list of operators, each of a specified arity. Equations are
-- given separately later (they are the reduction rules). Will also be given
-- proper types later.
public export
data Primitive : PrimitiveClass -> PrimitiveReducibility -> Arity -> Type where
  PrimTYPE : Primitive PrimNorm PrimIrreducible []
  PrimCode : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Explicit, "ty")]
  PrimQuote : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Implicit, "ty"), (Explicit, "val")]
  PrimSplice : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Implicit, "ty"), (Explicit, "val")]
  PrimLayout : Primitive PrimNorm PrimIrreducible []
  PrimZeroLayout : Primitive PrimNorm PrimIrreducible []
  PrimIdxLayout : Primitive PrimNorm PrimIrreducible []
  PrimPtrLayout : Primitive PrimNorm PrimIrreducible []
  PrimLayoutDyn : Primitive PrimNorm PrimIrreducible []
  PrimUNIT : Primitive PrimNorm PrimIrreducible []
  PrimTT : Primitive PrimNorm PrimIrreducible []
  PrimPadTy : Primitive PrimNorm PrimIrreducible [(Explicit, "bytes")]
  PrimPad : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes")]
  PrimIrrTy : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Explicit, "ty")]
  PrimIrr : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Implicit, "ty"), (Explicit, "val")]
  PrimStaLayoutDyn : Primitive PrimNorm PrimIrreducible [(Explicit, "staticBytes")]
  PrimType : Primitive PrimNorm PrimIrreducible [(Explicit, "bytes")]
  PrimSeqLayout : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]
  PrimSeqLayoutDyn : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]
  PrimSIGMA : (a : Name) -> Primitive PrimNorm PrimIrreducible [(Explicit, a), (Explicit, "rest")]
  PrimPAIR : (a : Name) -> Primitive PrimNorm PrimIrreducible
    [(Implicit, a), (Implicit, "rest"), (Explicit, "va"), (Explicit, "vrest")]
  PrimSigma : (a : Name) -> Primitive PrimNorm PrimIrreducible
    [(Implicit, "ba"), (Implicit, "bRest"), (Explicit, a), (Explicit, "rest")]
  PrimPair : (a : Name) -> Primitive PrimNorm PrimIrreducible
    [(Implicit, "ba"), (Implicit, "bRest"), (Implicit, a), (Implicit, "rest"), (Explicit, "va"), (Explicit, "vrest")]
  PrimIOTy : Primitive PrimNorm PrimIrreducible [(Implicit, "bt"), (Explicit, "t")]
  PrimIOBind : Primitive PrimNorm PrimIrreducible
    [(Implicit, "bt"), (Implicit, "t"), (Implicit, "a"), (Implicit, "b"), (Explicit, "x"), (Explicit, "f")]
  PrimIORet : Primitive PrimNorm PrimIrreducible
    [(Implicit, "bt"), (Implicit, "t"), (Implicit, "a"), (Explicit, "t")]


-- Can't be DecEq without writing out all cases smh
export
primEq : (a : Primitive k r ar) -> (b : Primitive k' r' ar') -> Maybe (a = b)
primEq PrimCode PrimCode = Just Refl
primEq PrimQuote PrimQuote = Just Refl
primEq PrimSplice PrimSplice = Just Refl
primEq PrimTYPE PrimTYPE = Just Refl
primEq PrimLayout PrimLayout = Just Refl
primEq PrimZeroLayout PrimZeroLayout = Just Refl
primEq PrimIdxLayout PrimIdxLayout = Just Refl
primEq PrimPtrLayout PrimPtrLayout = Just Refl
primEq PrimUNIT PrimUNIT = Just Refl
primEq PrimTT PrimTT = Just Refl
primEq PrimIrrTy PrimIrrTy = Just Refl
primEq PrimIrr PrimIrr = Just Refl
primEq PrimPadTy PrimPadTy = Just Refl
primEq PrimPad PrimPad = Just Refl
primEq PrimLayoutDyn PrimLayoutDyn = Just Refl
primEq PrimStaLayoutDyn PrimStaLayoutDyn = Just Refl
primEq (PrimSigma x) (PrimSigma x') = case decEq x x' of
  Yes Refl => Just Refl
  No contra => Nothing
primEq PrimType PrimType = Just Refl
primEq PrimSeqLayout PrimSeqLayout = Just Refl
primEq PrimSeqLayoutDyn PrimSeqLayoutDyn = Just Refl
primEq PrimIOTy PrimIOTy = Just Refl
primEq PrimIOBind PrimIOBind = Just Refl
primEq PrimIORet PrimIORet = Just Refl
primEq _ _ = Nothing

export
primName : Primitive k r ar -> String
primName PrimTYPE = "TYPE"
primName PrimCode = "Code"
primName PrimQuote = "quote"
primName PrimSplice = "splice"
primName PrimLayout = "Layout"
primName PrimZeroLayout = "zero"
primName PrimIdxLayout = "idx"
primName PrimPtrLayout = "ptr"
primName PrimLayoutDyn = "Layout?"
primName PrimUNIT = "UNIT"
primName PrimTT = "TT"
primName PrimPadTy = "Pad"
primName PrimPad = "pad"
primName PrimIrrTy = "Irr"
primName PrimIrr = "irr"
primName PrimStaLayoutDyn = "sta"
primName PrimType = "Type"
primName PrimSeqLayout = "seq"
primName PrimSeqLayoutDyn = "seq-dyn"
primName (PrimSIGMA a) = "SIGMA(" ++ a ++ ")"
primName (PrimPAIR a) = "PAIR(" ++ a ++ ")"
primName (PrimSigma a) = "Sigma(" ++ a ++ ")"
primName (PrimPair a) = "pair(" ++ a ++ ")"
primName PrimIOTy = "IO"
primName PrimIOBind = "io-bind"
primName PrimIORet = "io-ret"