-- Defining the primitives in the language
module Core.Primitives.Definitions

import Data.Singleton
import Common
import Core.Base
import Decidable.Equality
import Data.Maybe
import Data.DPair
import Data.Hashable
import Utils

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
  PrimTypeSta : Primitive PrimNorm PrimReducible PrimNative [(Explicit, "l")]
  PrimLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimLayoutDyn : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimSeqLayout : Primitive PrimNorm PrimReducible PrimNative [(Explicit, "a"), (Explicit, "b")]
  PrimSeqLayoutDyn : Primitive PrimNorm PrimReducible PrimNative [(Explicit, "a"), (Explicit, "b")]
  PrimZeroLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimIdxLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimPtrLayout : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimUNIT : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimTT : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimUnit : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimTt : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimFix : Primitive PrimNeu PrimReducible PrimNative [(Implicit, "l"), (Implicit, "A"), (Explicit, "a")]
  PrimFIX : Primitive PrimNeu PrimReducible PrimNative [(Implicit, "A"), (Explicit, "a")]

  PrimSIGMA : Primitive PrimNorm PrimIrreducible PrimDeclared [(Explicit, "A"), (Explicit, "B")]
  PrimPAIR : Primitive PrimNorm PrimIrreducible PrimDeclared
    [(Implicit, "A"), (Implicit, "B"), (Explicit, "a"), (Explicit, "b")]

  PrimSigma : Primitive PrimNorm PrimIrreducible PrimDeclared [(Implicit, "ba"), (Implicit, "bb"), (Explicit, "a"), (Explicit, "b")]
  PrimPair : Primitive PrimNorm PrimIrreducible PrimDeclared
     [(Implicit, "ba"), (Implicit, "bb"), (Implicit, "a"), (Implicit, "b"), (Explicit, "x"), (Explicit, "y")]

  PrimIO : Primitive PrimNorm PrimIrreducible PrimDeclared [(Implicit, "a"), (Explicit, "A")]
  PrimIOPure : Primitive PrimNorm PrimIrreducible PrimDeclared [(Implicit, "a"), (Explicit, "A"), (Explicit, "x")]

-- Can't be DecEq without writing out all cases smh
export
primEq : (a : Primitive k r na ar) -> (b : Primitive k' r' na' ar') -> Maybe (a ~=~ b)
primEq PrimTYPE PrimTYPE = Just Refl
primEq PrimTYPE _ = Nothing
primEq PrimCode PrimCode = Just Refl
primEq PrimCode _ = Nothing
primEq PrimQuote PrimQuote = Just Refl
primEq PrimQuote _ = Nothing
primEq PrimSplice PrimSplice = Just Refl
primEq PrimSplice _ = Nothing
primEq PrimSta PrimSta = Just Refl
primEq PrimSta _ = Nothing
primEq PrimTypeDyn PrimTypeDyn = Just Refl
primEq PrimTypeDyn _ = Nothing
primEq PrimTypeSta PrimTypeSta = Just Refl
primEq PrimTypeSta _ = Nothing
primEq PrimLayout PrimLayout = Just Refl
primEq PrimLayout _ = Nothing
primEq PrimLayoutDyn PrimLayoutDyn = Just Refl
primEq PrimLayoutDyn _ = Nothing
primEq PrimSeqLayout PrimSeqLayout = Just Refl
primEq PrimSeqLayout _ = Nothing
primEq PrimSeqLayoutDyn PrimSeqLayoutDyn = Just Refl
primEq PrimSeqLayoutDyn _ = Nothing
primEq PrimZeroLayout PrimZeroLayout = Just Refl
primEq PrimZeroLayout _ = Nothing
primEq PrimIdxLayout PrimIdxLayout = Just Refl
primEq PrimIdxLayout _ = Nothing
primEq PrimPtrLayout PrimPtrLayout = Just Refl
primEq PrimPtrLayout _ = Nothing
primEq PrimUNIT PrimUNIT = Just Refl
primEq PrimUNIT _ = Nothing
primEq PrimTT PrimTT = Just Refl
primEq PrimTT _ = Nothing
primEq PrimUnit PrimUnit = Just Refl
primEq PrimUnit _ = Nothing
primEq PrimTt PrimTt = Just Refl
primEq PrimTt _ = Nothing
primEq PrimSIGMA PrimSIGMA = Just Refl
primEq PrimSIGMA _ = Nothing
primEq PrimSigma PrimSigma = Just Refl
primEq PrimSigma _ = Nothing
primEq PrimIO PrimIO = Just Refl
primEq PrimIO _ = Nothing
primEq PrimPAIR PrimPAIR = Just Refl
primEq PrimPAIR _ = Nothing
primEq PrimPair PrimPair = Just Refl
primEq PrimPair _ = Nothing
primEq PrimIOPure PrimIOPure = Just Refl
primEq PrimIOPure _ = Nothing
primEq PrimFix PrimFix = Just Refl
primEq PrimFix _ = Nothing
primEq PrimFIX PrimFIX = Just Refl
primEq PrimFIX _ = Nothing

public export
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
primName PrimTypeSta = "Type"
primName PrimSeqLayout = "seq"
primName PrimSeqLayoutDyn = "seq-dyn"
primName PrimUNIT = "UNIT"
primName PrimTT = "TT"
primName PrimUnit = "Unit"
primName PrimTt = "tt"
primName PrimSIGMA = "SIGMA"
primName PrimSigma = "Sigma"
primName PrimIO = "IO"
primName PrimPAIR = "PAIR"
primName PrimPair = "pair"
primName PrimIOPure = "io-pure"
primName PrimFix = "fix"
primName PrimFIX = "FIX"

public export
Eq (Primitive k r na ar) where
  (==) p p' = isJust $ primEq p p'

public export
record PrimitiveAnyIrr where
  constructor MkPrimitiveAnyIrr
  {0 classif : PrimitiveClass}
  {0 reducibility : PrimitiveReducibility}
  {0 level : PrimitiveLevel}
  {0 arity : Arity}
  primitive : Primitive classif reducibility level arity

public export
record PrimitiveAny where
  constructor MkPrimitiveAny
  {classif : PrimitiveClass}
  {reducibility : PrimitiveReducibility}
  {level : PrimitiveLevel}
  {arity : Arity}
  primitive : Primitive classif reducibility level arity

public export
Eq PrimitiveAnyIrr where
  (==) p p' = isJust $ primEq p.primitive p'.primitive
  
congPrimitive : {0 a, b : PrimitiveAnyIrr} -> a.primitive ~=~ b.primitive -> a = b
congPrimitive {a = MkPrimitiveAnyIrr _} {b = MkPrimitiveAnyIrr _} Refl = Refl

public export
SemiDecEq PrimitiveAnyIrr where
  semiDecEq p p' = case (primEq p.primitive p'.primitive) of
    Just p => Just (congPrimitive p)
    Nothing => Nothing

public export
Hashable PrimitiveAnyIrr where
  -- @@Optim: use integers!
  hashWithSalt s p = hashWithSalt s (primName p.primitive)
  
public export
Show (Primitive k r na ar) where
  show p = primName p

public export
nameToPrim : String -> Maybe PrimitiveAny
nameToPrim "TYPE"    = Just $ MkPrimitiveAny PrimTYPE
nameToPrim "Code"    = Just $ MkPrimitiveAny PrimCode
nameToPrim "quote"   = Just $ MkPrimitiveAny PrimQuote
nameToPrim "splice"  = Just $ MkPrimitiveAny PrimSplice
nameToPrim "Layout"  = Just $ MkPrimitiveAny PrimLayout
nameToPrim "zero"    = Just $ MkPrimitiveAny PrimZeroLayout    
nameToPrim "idx"     = Just $ MkPrimitiveAny PrimIdxLayout     
nameToPrim "ptr"     = Just $ MkPrimitiveAny PrimPtrLayout     
nameToPrim "Layout?" = Just $ MkPrimitiveAny PrimLayoutDyn     
nameToPrim "sta"     = Just $ MkPrimitiveAny PrimSta           
nameToPrim "Type?"   = Just $ MkPrimitiveAny PrimTypeDyn       
nameToPrim "Type"   = Just $ MkPrimitiveAny PrimTypeSta
nameToPrim "seq"     = Just $ MkPrimitiveAny PrimSeqLayout     
nameToPrim "seq-dyn" = Just $ MkPrimitiveAny PrimSeqLayoutDyn  
nameToPrim "UNIT"    = Just $ MkPrimitiveAny PrimUNIT          
nameToPrim "TT"      = Just $ MkPrimitiveAny PrimTT            
nameToPrim "Unit"    = Just $ MkPrimitiveAny PrimUnit          
nameToPrim "tt"      = Just $ MkPrimitiveAny PrimTt            
nameToPrim "SIGMA"   = Just $ MkPrimitiveAny PrimSIGMA         
nameToPrim "Sigma"   = Just $ MkPrimitiveAny PrimSigma         
nameToPrim "IO"      = Just $ MkPrimitiveAny PrimIO            
nameToPrim "PAIR"    = Just $ MkPrimitiveAny PrimPAIR          
nameToPrim "pair"    = Just $ MkPrimitiveAny PrimPair          
nameToPrim "io-pure"    = Just $ MkPrimitiveAny PrimIOPure          
nameToPrim "FIX"    = Just $ MkPrimitiveAny PrimFIX          
nameToPrim "fix"    = Just $ MkPrimitiveAny PrimFix          
nameToPrim _   = Nothing

public export
nameToPrimId : {p : _} -> nameToPrim (primName p) === Just (MkPrimitiveAny p)
nameToPrimId {p = PrimTYPE}         = Refl
nameToPrimId {p = PrimCode}         = Refl
nameToPrimId {p = PrimQuote}        = Refl
nameToPrimId {p = PrimSplice}       = Refl
nameToPrimId {p = PrimSta}          = Refl
nameToPrimId {p = PrimTypeDyn}      = Refl
nameToPrimId {p = PrimTypeSta}      = Refl
nameToPrimId {p = PrimLayout}       = Refl
nameToPrimId {p = PrimLayoutDyn}    = Refl
nameToPrimId {p = PrimSeqLayout}    = Refl
nameToPrimId {p = PrimSeqLayoutDyn} = Refl
nameToPrimId {p = PrimZeroLayout}   = Refl
nameToPrimId {p = PrimIdxLayout}    = Refl
nameToPrimId {p = PrimPtrLayout}    = Refl
nameToPrimId {p = PrimUNIT}         = Refl
nameToPrimId {p = PrimTT}           = Refl
nameToPrimId {p = PrimUnit}         = Refl
nameToPrimId {p = PrimTt}           = Refl
nameToPrimId {p = PrimSIGMA}        = Refl
nameToPrimId {p = PrimPAIR}         = Refl
nameToPrimId {p = PrimSigma}        = Refl
nameToPrimId {p = PrimPair}         = Refl
nameToPrimId {p = PrimIO}           = Refl
nameToPrimId {p = PrimIOPure}       = Refl  
nameToPrimId {p = PrimFix}        = Refl
nameToPrimId {p = PrimFIX}        = Refl
