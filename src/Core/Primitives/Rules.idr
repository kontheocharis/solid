-- All the declarative reduction rules for primitives.
module Core.Primitives.Rules

import Data.Singleton
import Common
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation

%default covering

-- Some shorthands

public export
sCode : Tm ns -> Tm ns -> Tm ns
sCode by ty = sPrim PrimCode [(Val _, by), (Val _, ty)]

public export
sQuote : Tm ns -> Tm ns -> Tm ns -> Tm ns
sQuote by ty val = sPrim PrimQuote [(Val _, by), (Val _, ty), (Val _, val)]

public export
sSplice : Tm ns -> Tm ns -> Tm ns -> Tm ns
sSplice by ty val = SynPrimNormal (PrimSplice $$ [(Val _, by), (Val _, ty), (Val _, val)])

-- Compile-time bytes as partially-static
public export
staLayoutDyn : Tm ns -> Tm ns
staLayoutDyn b = SynPrimNormal (PrimSta $$ [(Val _, b)])

public export
layout : Ty ns
layout = SynPrimNormal (PrimLayout $$ [])

public export
layoutDyn : Tm ns
layoutDyn = SynPrimNormal (PrimLayoutDyn $$ [])

-- `Type b` for some *compile-time* byte size `b`, object-level type of types.
public export
sizedObjType : (b : Tm ns) -> Ty ns
sizedObjType b = SynPrimNormal (PrimType $$ [(Val _, staLayoutDyn b)])

public export
dynObjType : Tm ns -> Ty ns
dynObjType b = SynPrimNormal (PrimType $$ [(Val _, b)])

-- The `0` bytes value.
public export
zeroLayout : Tm ns
zeroLayout = SynPrimNormal (PrimZeroLayout $$ [])

public export
idxLayout : Tm ns
idxLayout = SynPrimNormal (PrimIdxLayout $$ [])

public export
ptrLayout : Tm ns
ptrLayout = SynPrimNormal (PrimPtrLayout $$ [])

-- `TYPE`, meta-level type of types.
public export
mtaType : Ty ns
mtaType = SynPrimNormal (PrimTYPE $$ [])

-- Get either `Type 0` or `TYPE` depending on the stage.
public export
typeOfTypesForStage : Stage -> Ty ns
typeOfTypesForStage Mta = mtaType
typeOfTypesForStage Obj = sizedObjType zeroLayout

public export
mtaUnit : Ty ns
mtaUnit = SynPrimNormal (PrimUNIT $$ [])

public export
layoutDynAdd : Tm ns -> Tm ns -> Tm ns
layoutDynAdd a b = SynPrimNormal (PrimSeqLayoutDyn $$ [(Val _, a), (Val _, b)])

-- Reduction rules:

-- Note: for every primitive that might reduce on an argument, in addition to
-- matching the the actual shape that it reduces on, we must also match on
-- (Glued _). We must do this for each argument that might cause a reduction. In
-- each case we must form a new glued term as a result, which lazily unfolds the
-- argument and recurses.

primAddBYTES : Term Value ns -> Term Value ns -> Term Value ns
primAddBYTES (SimpPrimNormal (SimpApplied PrimZeroLayout [])) b = b
primAddBYTES a (SimpPrimNormal (SimpApplied PrimZeroLayout [])) = a
primAddBYTES a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimSeqLayout [(Val _, a), (Val _, b)] (primAddBYTES (simplified a') b)))
primAddBYTES a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimSeqLayout [(Val _, a), (Val _, b)] (primAddBYTES a (simplified b'))))
primAddBYTES a b = SimpPrimNormal (SimpApplied PrimSeqLayout [(Val _, a), (Val _, b)])

primAddBytes : Term Value ns -> Term Value ns -> Term Value ns
primAddBytes (SimpPrimNormal (SimpApplied PrimSta [(_, a)])) (SimpPrimNormal (SimpApplied PrimSta [(_, b)]))
  = SimpPrimNormal (SimpApplied PrimSta [(Val _, primAddBYTES a b)])
primAddBytes (SimpPrimNormal (SimpApplied PrimSta [(_, SimpPrimNormal (SimpApplied PrimZeroLayout []))])) b = b
primAddBytes a (SimpPrimNormal (SimpApplied PrimSta [(_, SimpPrimNormal (SimpApplied PrimZeroLayout []))])) = a
primAddBytes a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimSeqLayoutDyn [(Val _, a), (Val _, b)] (primAddBytes (simplified a') b)))
primAddBytes a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimSeqLayoutDyn [(Val _, a), (Val _, b)] (primAddBytes a (simplified b'))))
primAddBytes a b = SimpPrimNormal (SimpApplied PrimSeqLayoutDyn [(Val _, a), (Val _, b)])

public export
Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value) where
  eval env (($$) {r = PrimIrreducible} {k = PrimNorm} p sp) = SimpPrimNormal (SimpApplied p (eval env sp))
  eval env (($$) {r = PrimIrreducible} {k = PrimNeu} p sp) = SimpApps (PrimNeutral (SimpApplied p (eval env sp)) $$ [])
  eval env (PrimSeqLayout $$ [(_, a), (_, b)]) = primAddBYTES (eval env a) (eval env b)
  eval env (PrimSeqLayoutDyn $$ [(_, a), (_, b)]) = primAddBytes (eval env a) (eval env b)

-- Context-aware domain
-- 
-- This is so that operations can be generic over the domain. However,
-- to do this we need the size of the context to be known when the domain is
-- a value, so that we can eval/quote freely.
public export
data DomainIn : Domain -> Ctx -> Type where
  SyntaxIn : DomainIn Syntax ns
  ValueIn : Size ns -> DomainIn Value ns