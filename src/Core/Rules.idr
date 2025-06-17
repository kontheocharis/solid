-- All the declarative typing and reduction rules for primitives.
module Core.Rules

import Data.Singleton
import Common
import Core.Base
import Core.Primitives
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
embedBytes : Tm ns -> Tm ns
embedBytes b = SynPrimNormal (PrimEmbedBYTES $$ [(Val _, b)])

public export
staBytes : Ty ns
staBytes = SynPrimNormal (PrimBYTES $$ [])

public export
psBytes : Tm ns
psBytes = SynPrimNormal (PrimBytes $$ [])

-- `Type b` for some *compile-time* byte size `b`, object-level type of types.
public export
sizedObjType : (b : Tm ns) -> Ty ns
sizedObjType b = SynPrimNormal (PrimDyn $$ [(Val _, embedBytes b)])

public export
dynObjType : Tm ns -> Ty ns
dynObjType b = SynPrimNormal (PrimDyn $$ [(Val _, b)])

-- The `0` bytes value.
public export
zeroBytes : Tm ns
zeroBytes = SynPrimNormal (PrimZeroBYTES $$ [])

public export
sizeBytes : Tm ns
sizeBytes = SynPrimNormal (PrimSizeBYTES $$ [])

public export
ptrBytes : {d : Domain} -> Term d ns
ptrBytes {d = Syntax} = SynPrimNormal (PrimPtrBYTES $$ [])
ptrBytes {d = Value} = SimpPrimNormal (SimpApplied PrimPtrBYTES [])

-- `TYPE`, meta-level type of types.
public export
mtaType : Ty ns
mtaType = SynPrimNormal (PrimTYPE $$ [])

-- Get either `Type 0` or `TYPE` depending on the stage.
public export
typeOfTypesForStage : Stage -> Ty ns
typeOfTypesForStage Mta = mtaType
typeOfTypesForStage Obj = sizedObjType zeroBytes

public export
mtaUnit : Ty ns
mtaUnit = SynPrimNormal (PrimUNIT $$ [])

public export
psBytesAdd : Tm ns -> Tm ns -> Tm ns
psBytesAdd a b = SynPrimNormal (PrimAddBytes $$ [(Val _, a), (Val _, b)])

public export
primN : PrimitiveApplied PrimNorm Syntax NA ns -> Term Syntax ns
primN = SynPrimNormal

public export
unitForStage : Stage -> Ty ns
unitForStage Mta = primN $ (PrimUNIT $$ [])
unitForStage Obj = primN $ (PrimPadTy $$ [(Val _, embedBytes zeroBytes)])

public export
ttForStage : Stage -> Ty ns
ttForStage Mta = primN $ (PrimTT $$ [])
ttForStage Obj = primN $ (PrimPad $$ [(Val _, embedBytes zeroBytes)])

-- Typing rules:

-- annot : (a : Ty ns) -> Stage -> Annot ns
-- annot a Mta = MkAnnot a Mta

-- Types of the arguments and return values of all the primitives
public export
primTy : (p : Primitive k r ar) -> (Tel ar ValTy ns, ValTy (ns ::< ar))
-- primTy PrimTYPE = ([], MkAnnot mtaType Mta)
-- primTy PrimCode = ([MkAnnot psBytes Obj, MkAnnot (objType (var "bytes")) Obj], MkAnnot mtaType Mta)
-- primTy PrimQuote = ([MkAnnot psBytes Obj, MkAnnot (objType (var "bytes")) Obj, MkAnnot (var "ty") Obj], MkAnnot (sCode (var "bytes") (var "ty")) Mta)
-- primTy PrimSplice = ([MkAnnot psBytes Obj, MkAnnot (objType (var "bytes")) Obj, MkAnnot (sCode (var "bytes") (var "ty")) Mta], MkAnnot (var "ty") Obj)
-- primTy PrimBYTES = ([], MkAnnot mtaType Mta)
-- primTy PrimZeroBYTES = ([], MkAnnot mtaBytes Mta)
-- primTy PrimSizeBYTES = ([], MkAnnot mtaBytes Mta)
-- primTy PrimPtrBYTES = ([], MkAnnot mtaBytes Mta)
-- primTy PrimBytes = ([], MkAnnot (sizedObjType sizeBytes) Obj)
-- primTy PrimUNIT = ([], MkAnnot mtaType Mta)
-- primTy PrimTT = ([], MkAnnot mtaUnit Mta)
-- primTy PrimIrrTy = ([MkAnnot psBytes Obj, MkAnnot (sizedObjType (var "bytes")) Obj], MkAnnot (sizedObjType zeroBytes) Obj)
-- primTy PrimIrr = ([MkAnnot psBytes Obj, MkAnnot (sizedObjType (var "bytes")) Obj, MkAnnot (var "ty") Obj], MkAnnot (primN (PrimIrrTy $$ [var "bytes", var "ty"])) Obj)
-- primTy PrimPadTy = ([MkAnnot psBytes Obj], MkAnnot (sizedObjType (var "bytes")) Obj)
-- primTy PrimPad = ([MkAnnot psBytes Obj], MkAnnot (primN (PrimPadTy $$ [var "bytes"])) Obj)
-- primTy PrimEmbedBYTES = ([MkAnnot mtaBytes Mta], MkAnnot psBytes Obj)
-- primTy PrimUnsized = ([MkAnnot psBytes Obj], MkAnnot (sizedObjType zeroBytes) Obj)
-- primTy PrimAddBYTES = ([MkAnnot mtaBytes Mta, MkAnnot mtaBytes Mta], MkAnnot mtaBytes Mta)
-- primTy PrimAddBytes = ([MkAnnot psBytes Obj, MkAnnot psBytes Obj], MkAnnot psBytes Obj)
-- primTy (PrimSIGMA a) = ([MkAnnot mtaType Mta, MkAnnot (sMtaPi (Explicit, "x") (var a) mtaType) Mta], MkAnnot mtaType Mta)
-- primTy (PrimPAIR a) = ([
--     MkAnnot mtaType Mta,
--     MkAnnot (sMtaPi (Explicit, "x") (var a) mtaType) Mta,
--     MkAnnot (var a) Mta,
--     MkAnnot (varApp "rest" (Explicit, "x") (var "va")) Mta
--   ], MkAnnot (primN (PrimSIGMA a $$ [var a, var "rest"])) Mta)
-- primTy (PrimSigma a) = ([
--     MkAnnot psBytes Obj,
--     MkAnnot psBytes Obj,
--     MkAnnot (objType (var "ba")) Obj,
--     MkAnnot (sMtaPi (Explicit, "x") (var a) (objType (var "bRest"))) Obj
--   ], MkAnnot (objType (psBytesAdd (var "ba") (var "bRest"))) Obj)
-- primTy (PrimPair a) = ([
--     MkAnnot psBytes Obj,
--     MkAnnot psBytes Obj,
--     MkAnnot (objType (var "ba")) Obj,
--     MkAnnot (sMtaPi (Explicit, "x") (var a) (objType (var "bRest"))) Obj,
--     MkAnnot (var a) Obj,
--     MkAnnot (varApp "rest" (Explicit, "x") (var "va")) Obj
--   ], MkAnnot (primN (PrimSigma a $$ [var "ba", var "bRest", var a, var "rest"])) Obj)


-- Reduction rules:

-- Note: for every primitive that might reduce on an argument, in addition to
-- matching the the actual shape that it reduces on, we must also match on
-- (Glued _). We must do this for each argument that might cause a reduction. In
-- each case we must form a new glued term as a result, which lazily unfolds the
-- argument and recurses.

primAddBYTES : Term Value ns -> Term Value ns -> Term Value ns
primAddBYTES (SimpPrimNormal (SimpApplied PrimZeroBYTES [])) b = b
primAddBYTES a (SimpPrimNormal (SimpApplied PrimZeroBYTES [])) = a
primAddBYTES a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimAddBYTES [(Val _, a), (Val _, b)] (primAddBYTES (simplified a') b)))
primAddBYTES a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimAddBYTES [(Val _, a), (Val _, b)] (primAddBYTES a (simplified b'))))
primAddBYTES a b = SimpPrimNormal (SimpApplied PrimAddBYTES [(Val _, a), (Val _, b)])

primAddBytes : Term Value ns -> Term Value ns -> Term Value ns
primAddBytes (SimpPrimNormal (SimpApplied PrimEmbedBYTES [(_, a)])) (SimpPrimNormal (SimpApplied PrimEmbedBYTES [(_, b)]))
  = SimpPrimNormal (SimpApplied PrimEmbedBYTES [(Val _, primAddBYTES a b)])
primAddBytes (SimpPrimNormal (SimpApplied PrimEmbedBYTES [(_, SimpPrimNormal (SimpApplied PrimZeroBYTES []))])) b = b
primAddBytes a (SimpPrimNormal (SimpApplied PrimEmbedBYTES [(_, SimpPrimNormal (SimpApplied PrimZeroBYTES []))])) = a
primAddBytes a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimAddBytes [(Val _, a), (Val _, b)] (primAddBytes (simplified a') b)))
primAddBytes a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimAddBytes [(Val _, a), (Val _, b)] (primAddBytes a (simplified b'))))
primAddBytes a b = SimpPrimNormal (SimpApplied PrimAddBytes [(Val _, a), (Val _, b)])

public export
Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value) where
  eval env (($$) {r = PrimIrreducible} {k = PrimNorm} p sp) = SimpPrimNormal (SimpApplied p (eval env sp))
  eval env (($$) {r = PrimIrreducible} {k = PrimNeu} p sp) = SimpApps (PrimNeutral (SimpApplied p (eval env sp)) $$ [])
  eval env (PrimAddBYTES $$ [(_, a), (_, b)]) = primAddBYTES (eval env a) (eval env b)
  eval env (PrimAddBytes $$ [(_, a), (_, b)]) = primAddBytes (eval env a) (eval env b)

-- Context-aware domain
-- 
-- This is so that operations can be generic over the domain. However,
-- to do this we need the size of the context to be known when the domain is
-- a value, so that we can eval/quote freely.
public export
data DomainIn : Domain -> Ctx -> Type where
  SyntaxIn : DomainIn Syntax ns
  ValueIn : Size ns -> DomainIn Value ns

-- Create a primitive in the given domain
public export
prim : {k : PrimitiveClass} -> {r : PrimitiveReducibility}
  -> DomainIn d ns
  -> Primitive k r ar
  -> Spine ar (Term d) ns
  -> Term d ns
prim SyntaxIn p sp = sPrim p sp
prim (ValueIn s) p sp = eval {over = ValTy} id (sPrim p (quote sp))

public export
vPrim : {k : PrimitiveClass} -> {r : PrimitiveReducibility}
  -> Size ns
  => Primitive k r ar
  -> Spine ar Val ns
  -> Val ns
vPrim @{s} = prim (ValueIn s)