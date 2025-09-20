-- All the declarative reduction rules for primitives.
module Core.Primitives.Rules

import Data.Singleton
import Common
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Debug.Trace
import Utils

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
sizedObjType b = SynPrimNormal (PrimTypeDyn $$ [(Val _, staLayoutDyn b)])

public export
dynObjType : Tm ns -> Ty ns
dynObjType b = SynPrimNormal (PrimTypeDyn $$ [(Val _, b)])

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
layoutAdd : Tm ns -> Tm ns -> Tm ns
layoutAdd a b = SynPrimNormal (PrimSeqLayoutDyn $$ [(Val _, a), (Val _, b)])

-- Reduction rules:

-- Note: for every primitive that might reduce on an argument, in addition to
-- matching the the actual shape that it reduces on, we must also match on
-- (Glued _). We must do this for each argument that might cause a reduction. In
-- each case we must form a new glued term as a result, which lazily unfolds the
-- argument and recurses.

primSeqLayout' : Term Value ns -> Term Value ns -> Term Value ns

primSeqLayout : Term Value ns -> Term Value ns -> Maybe (Term Value ns)
primSeqLayout (SimpPrimNormal (SimpApplied PrimZeroLayout [])) b = Just b
primSeqLayout a (SimpPrimNormal (SimpApplied PrimZeroLayout [])) = Just a
primSeqLayout a@(Glued a') b = Just $ Glued (LazyPrimNormal (LazyApplied PrimSeqLayout [(Val _, a), (Val _, b)] (primSeqLayout' (simplified a') b)))
primSeqLayout a b@(Glued b') = Just $ Glued (LazyPrimNormal (LazyApplied PrimSeqLayout [(Val _, a), (Val _, b)] (primSeqLayout' a (simplified b'))))
primSeqLayout _ _ = Nothing

primSeqLayout' a b = case primSeqLayout a b of
  Just r => r
  Nothing => SimpPrimNormal (SimpApplied PrimSeqLayout [(Val _, a), (Val _, b)])

primSeqLayoutDyn' : Term Value ns -> Term Value ns -> Term Value ns

primSeqLayoutDyn : Term Value ns -> Term Value ns -> Maybe (Term Value ns)
primSeqLayoutDyn (SimpPrimNormal (SimpApplied PrimSta [(_, a)])) (SimpPrimNormal (SimpApplied PrimSta [(_, b)]))
  = Just $ SimpPrimNormal (SimpApplied PrimSta [(Val _, primSeqLayout' a b)])
primSeqLayoutDyn (SimpPrimNormal (SimpApplied PrimSta [(_, SimpPrimNormal (SimpApplied PrimZeroLayout []))])) b = Just b
primSeqLayoutDyn a (SimpPrimNormal (SimpApplied PrimSta [(_, SimpPrimNormal (SimpApplied PrimZeroLayout []))])) = Just a
primSeqLayoutDyn a@(Glued a') b = Just $ Glued (LazyPrimNormal (LazyApplied PrimSeqLayoutDyn [(Val _, a), (Val _, b)] (primSeqLayoutDyn' (simplified a') b)))
primSeqLayoutDyn a b@(Glued b') = Just $ Glued (LazyPrimNormal (LazyApplied PrimSeqLayoutDyn [(Val _, a), (Val _, b)] (primSeqLayoutDyn' a (simplified b'))))
primSeqLayoutDyn a b = Nothing

primSeqLayoutDyn' a b = case primSeqLayoutDyn a b of
  Just r => r
  Nothing => SimpPrimNormal (SimpApplied PrimSeqLayout [(Val _, a), (Val _, b)])
  
primApps : Primitive k PrimReducible na ar -> Spine ar (Term Value) ns -> Maybe (Term Value ns)
primApps' : {k : _} -> Primitive k PrimReducible na ar -> Spine ar (Term Value) ns -> Term Value ns

public export
Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value) where
  eval env (($$) {r = PrimIrreducible} {k = PrimNorm} p sp) = SimpPrimNormal (SimpApplied p (eval env sp))
  eval env (($$) {r = PrimIrreducible} {k = PrimNeu} p sp) = SimpApps (PrimNeutral (SimpApplied p (eval env sp)) $$ [])
  eval env (($$) {r = PrimReducible} x sp) = primApps' x (eval env sp)

primApps PrimTypeSta [(_, l)] = Just $ Glued (LazyPrimNormal (LazyApplied PrimTypeSta [(Val _, l)]
  (SimpPrimNormal (SimpApplied PrimTypeDyn [(Val _, SimpPrimNormal (SimpApplied PrimSta [(Val _, l)]))]))))
primApps PrimSeqLayout [(_, a), (_, b)] = primSeqLayout a b
primApps PrimSeqLayoutDyn [(_, a), (_, b)] = primSeqLayoutDyn a b
primApps PrimFix sp@[_, _, (_, x)] =
  let wrap = \s : Lazy (Val ns) => Glued (LazyApps (PrimNeutral (LazyApplied PrimFix sp s) $$ []) s) in
  let simplified : Lazy (Val ns)
      simplified = delay $ apps x [(Val (Explicit, "x"), wrap simplified)]
  in Just (wrap simplified)
primApps PrimFIX sp@[_, (_, x)] =
  let wrap = \s : Lazy (Val ns) => Glued (LazyApps (PrimNeutral (LazyApplied PrimFIX sp s) $$ []) s) in
  let simplified : Lazy (Val ns)
      simplified = delay $ apps x [(Val (Explicit, "x"), wrap simplified)]
  in Just (wrap simplified)

primApps' p sp = case primApps p sp of
  Just r => r
  Nothing => case k of
    PrimNorm => SimpPrimNormal (SimpApplied p sp)
    PrimNeu => SimpApps (PrimNeutral (SimpApplied p sp) $$ [])

-- Context-aware domain
-- 
-- This is so that operations can be generic over the domain. However,
-- to do this we need the size of the context to be known when the domain is
-- a value, so that we can eval/quote freely.
public export
data DomainIn : Domain -> Ctx -> Type where
  SyntaxIn : DomainIn Syntax ns
  ValueIn : Size ns -> DomainIn Value ns

-- Create a primitive value
--
-- Always calls eval if the primitive is reducible, to wrap it in lazy if needed.
public export covering
vPrim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility} -> Primitive k r na ar -> Spine ar Val ns -> Val ns
vPrim {k = PrimNorm} {r = PrimIrreducible} p sp = SimpPrimNormal (SimpApplied p sp)
vPrim {k = PrimNeu} {r = PrimIrreducible} p sp = SimpApps (PrimNeutral (SimpApplied p sp) $$ [])
vPrim {r = PrimReducible} p sp = eval id $ sPrim p (quote sp)

export
primResolver : Monad m => Resolver m (Val ns)
primResolver = repeatedly $ \case
  (SimpApps ((PrimNeutral (SimpApplied {r = PrimReducible} p sp)) $$ sp')) => pure $ apps <$> primApps p sp <*> pure sp'
  (SimpPrimNormal (SimpApplied {r = PrimReducible} p sp)) => pure $ primApps p sp
  _ => pure Nothing