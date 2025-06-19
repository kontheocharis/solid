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
  PrimBYTES : Primitive PrimNorm PrimIrreducible []
  PrimZeroBYTES : Primitive PrimNorm PrimIrreducible []
  PrimSizeBYTES : Primitive PrimNorm PrimIrreducible []
  PrimPtrBYTES : Primitive PrimNorm PrimIrreducible []
  PrimBytes : Primitive PrimNorm PrimIrreducible []
  PrimUNIT : Primitive PrimNorm PrimIrreducible []
  PrimTT : Primitive PrimNorm PrimIrreducible []
  PrimPadTy : Primitive PrimNorm PrimIrreducible [(Explicit, "bytes")]
  PrimPad : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes")]
  PrimIrrTy : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Explicit, "ty")]
  PrimIrr : Primitive PrimNorm PrimIrreducible [(Implicit, "bytes"), (Implicit, "ty"), (Explicit, "val")]
  PrimEmbedBYTES : Primitive PrimNorm PrimIrreducible [(Explicit, "staticBytes")]
  PrimDyn : Primitive PrimNorm PrimIrreducible [(Explicit, "bytes")]
  PrimAddBYTES : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]
  PrimAddBytes : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]
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
primEq PrimBYTES PrimBYTES = Just Refl
primEq PrimZeroBYTES PrimZeroBYTES = Just Refl
primEq PrimSizeBYTES PrimSizeBYTES = Just Refl
primEq PrimPtrBYTES PrimPtrBYTES = Just Refl
primEq PrimUNIT PrimUNIT = Just Refl
primEq PrimTT PrimTT = Just Refl
primEq PrimIrrTy PrimIrrTy = Just Refl
primEq PrimIrr PrimIrr = Just Refl
primEq PrimPadTy PrimPadTy = Just Refl
primEq PrimPad PrimPad = Just Refl
primEq PrimBytes PrimBytes = Just Refl
primEq PrimEmbedBYTES PrimEmbedBYTES = Just Refl
primEq (PrimSigma x) (PrimSigma x') = case decEq x x' of
  Yes Refl => Just Refl
  No contra => Nothing
primEq PrimDyn PrimDyn = Just Refl
primEq PrimAddBYTES PrimAddBYTES = Just Refl
primEq PrimAddBytes PrimAddBytes = Just Refl
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
primName PrimBYTES = "BYTES"
primName PrimZeroBYTES = "zero"
primName PrimSizeBYTES = "size"
primName PrimPtrBYTES = "ptr"
primName PrimBytes = "Bytes"
primName PrimUNIT = "UNIT"
primName PrimTT = "TT"
primName PrimPadTy = "PadTy"
primName PrimPad = "Pad"
primName PrimIrrTy = "IrrTy"
primName PrimIrr = "Irr"
primName PrimEmbedBYTES = "embed-BYTES"
primName PrimDyn = "Dyn"
primName PrimAddBYTES = "add-bytes"
primName PrimAddBytes = "add-bytes"
primName (PrimSIGMA a) = "SIGMA(" ++ a ++ ")"
primName (PrimPAIR a) = "PAIR(" ++ a ++ ")"
primName (PrimSigma a) = "Sigma(" ++ a ++ ")"
primName (PrimPair a) = "Pair(" ++ a ++ ")"
primName PrimIOTy = "IO"
primName PrimIOBind = "io-bind"
primName PrimIORet = "io-ret"


