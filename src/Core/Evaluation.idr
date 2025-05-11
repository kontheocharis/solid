-- Defining NbE for the core language
module Core.Evaluation

import Utils
import Core.Base
import Core.Syntax

%default covering -- won't bother with the totality checker here

-- Terms can be evalued and quoted (given later)
public export
0 EvalTm : Type
EvalTm = Eval (Term Value) (Term Syntax) (Term Value)

public export
0 WeakVal : Type
WeakVal = Weak (Term Value)

public export
0 QuoteVal : Type
QuoteVal = Quote (Term Value) (Term Syntax)

-- We will give the reduction rules of primitives separately
public export
0 EvalPrim : Type
EvalPrim = forall k, e . Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value)

-- Evaluation and quoting for all the syntax:

-- Every callable binding value can be applied to a term.
public export
callBinding : EvalTm => Binding s Callable Value ns -> Term Value ns -> Term Value ns
callBinding (Bound s n BindLam (Closure env body)) arg = eval (env :< arg) body

-- Every thunk can be forced.
public export
forceThunk : EvalTm => Binding s Thunk Value ns -> Term Value ns
forceThunk (Bound s n (BindLet _ v) (Closure env body)) = eval (env :< v) body

public export
QuoteVal => Quote (PrimitiveApplied k Value e) (PrimitiveApplied k Syntax NA) where
  quote s (SimpApplied h sp) = h $$ quote s sp
  quote s (LazyApplied h sp _) = h $$ quote s sp

public export
WeakVal => Weak (PrimitiveApplied k Value e) where
  weak e (SimpApplied h sp) = SimpApplied h (weak e sp)
  weak e (LazyApplied h sp gl) = LazyApplied h (weak e sp) (weak e gl)

public export
Eval over (Term d) (Term d') => Eval over (Binder md r d) (Binder md r d') where
  eval env b = mapBinder (eval env) b

public export
Quote (Term d) (Term d') => Quote (Binder md r d) (Binder md r d') where
  quote s b = mapBinder (quote s) b

public export
WeakVal => Weak (Binder md r Value) where
  weak e b = mapBinder (weak e) b

public export
Eval (Term Value) (Variable Syntax) (Term Value) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

public export
Quote (Variable Value) (Variable Syntax) where
  quote s (Level l) = Index (quote s l)

public export
(WeakVal) => Weak (Variable Value) where
  weak s (Level l) = Level (weak s l)

public export
WeakVal => Vars (Term Value) where
  here s = SimpApps (ValVar (Level (lastLvl s)) $$ [])

public export
Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

public export
(WeakVal, QuoteVal, EvalTm) => Quote (Body Value n) (Body Syntax n) where
  quote s (Closure env t) = Delayed (quote {val = Term Value} (SS s) (eval (lift s env) t))

public export
WeakVal => Weak (Body Value n) where
  weak e (Closure env t) = Closure (env . e) t

public export
EvalTm => Eval (Term Value) (Binding s r Syntax) (Binding s r Value) where
  eval env (Bound s n bind body) = Bound s n (eval env bind) (eval env body)

public export
(WeakVal, QuoteVal, EvalTm) => Quote (Binding s r Value) (Binding s r Syntax) where
  quote s (Bound s' n bind body) = Bound s' n (quote s bind) (quote s body)

public export
WeakVal => Weak (Binding s r Value) where
  weak s (Bound s' n bind body) = Bound s' n (weak s bind) (weak s body)

-- Helper to apply a value to a spine.
--
-- This is the only place where it could crash if there is a bug, because
-- the syntax is not well-typed (only well-scoped).
public export
apps : EvalTm => Term Value ns -> Spine ar (Term Value) ns -> Term Value ns
apps (Glued (LazyApps (v $$ sp) gl)) sp' = Glued (LazyApps (v $$ sp ++ sp') (apps gl sp'))
apps (SimpApps (v $$ sp)) sp' = SimpApps (v $$ sp ++ sp')
apps (MtaCallable t) [] = MtaCallable t
apps (MtaCallable t) (x :: sp') = apps (callBinding t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) (x :: sp') = apps (callBinding t x) sp'
apps (RigidBinding _ _) _ = error "impossible"
apps (SimpPrimNormal _) sp' = error "impossible"
apps (Glued (LazyPrimNormal _)) sp' = error "impossible"

public export
(EvalTm, EvalPrim) => Eval (Term Value) (Head Syntax NA) (Term Value) where
  eval env (SynVar v) = eval env v
  eval env (SynMeta v) = SimpApps (ValMeta v $$ [])
  eval env (SynBinding md Rigid t) = RigidBinding md (eval env t)
  eval env (SynBinding Obj Callable t) = Glued (LazyApps (ObjCallable (eval env t) $$ []) (SimpObjCallable (eval env t)))
  eval env (SynBinding Obj Thunk t) = Glued (LazyApps (ObjLazy (eval env t) $$ []) (forceThunk {s = Obj} (eval env t)))
  eval env (SynBinding Mta Callable t) = MtaCallable (eval env t)
  eval env (SynBinding Mta Thunk t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

public export
(WeakVal, QuoteVal, EvalTm) => Quote (Head Value hk) (Head Syntax NA) where
  quote s (ValVar v) = SynVar (quote s v)
  quote s (ValMeta m) = SynMeta m
  quote s (ObjCallable t) = SynBinding Obj Callable (quote s t)
  quote s (ObjLazy t) = SynBinding Obj Thunk (quote s t)
  quote s (PrimNeutral p) = PrimNeutral {e = NA} (quote s p)

public export
WeakVal => Weak (Head Value hk) where
  weak s (ValVar v) = ValVar (weak s v)
  weak s (ValMeta m) = ValMeta m
  weak s (ObjCallable t) = ObjCallable (weak s t)
  weak s (ObjLazy t) = ObjLazy (weak s t)
  weak s (PrimNeutral p) = PrimNeutral (weak s p)

public export
(WeakVal, QuoteVal, EvalTm) => Quote (HeadApplied Value hk) (HeadApplied Syntax NA) where
  quote s (($$) {ar = ar} h sp) = ($$) {ar = ar} (quote s h) (quote s sp)

public export
WeakVal => Weak (HeadApplied Value hk) where
  weak e (h $$ sp) = weak e h $$ weak e sp

public export
Weak (Term Value) where
  weak e (Glued (LazyApps a f)) = Glued (LazyApps (weak e a) (weak e f))
  weak e (Glued (LazyPrimNormal a)) = Glued (LazyPrimNormal (weak e a))
  weak e (SimpApps a) = SimpApps (weak e a)
  weak e (MtaCallable c) = MtaCallable (weak e c)
  weak e (SimpObjCallable c) = SimpObjCallable (weak e c)
  weak e (RigidBinding md c) = RigidBinding md (weak e c)
  weak e (SimpPrimNormal p) = SimpPrimNormal (weak e p)

public export
EvalPrim => Eval (Term Value) (Term Syntax) (Term Value) where
  eval env (SynApps (($$) {ar = ar} h sp)) = apps {ar = ar} (eval env h) (eval env sp)
  eval env (RigidBinding md t) = RigidBinding md (eval env t)
  eval env (SynPrimNormal prim) = eval env prim

public export
EvalPrim => Quote (Term Value) (Term Syntax) where
  quote s (Glued (LazyApps a _)) = SynApps (quote s a)
  quote s (Glued (LazyPrimNormal a)) = SynPrimNormal (quote s a)
  quote s (SimpApps a) = SynApps (quote s a)
  quote s (MtaCallable c) = SynApps (SynBinding Mta Callable (quote s c) $$ [])
  quote s (SimpObjCallable c) = SynApps (SynBinding Obj Callable (quote s c) $$ [])
  quote s (RigidBinding md c) = RigidBinding md (quote s c)
  quote s (SimpPrimNormal p) = SynPrimNormal (quote s p)

-- Primitives:

-- Note: for every primitive that might reduce on an argument, in addition to
-- matching the the actual shape that it reduces on, we must also match on
-- (Glued _). We must do this for each argument that might cause a reduction. In
-- each case we must form a new glued term as a result, which lazily unfolds the
-- argument and recurses.

primAddBYTES : Term Value ns -> Term Value ns -> Term Value ns
primAddBYTES (SimpPrimNormal (SimpApplied PrimZeroBYTES [])) b = b
primAddBYTES a (SimpPrimNormal (SimpApplied PrimZeroBYTES [])) = a
primAddBYTES a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimAddBYTES [a, b] (primAddBYTES (simplified a') b)))
primAddBYTES a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimAddBYTES [a, b] (primAddBYTES a (simplified b'))))
primAddBYTES a b = SimpPrimNormal (SimpApplied PrimAddBYTES [a, b])

primAddBytes : Term Value ns -> Term Value ns -> Term Value ns
primAddBytes (SimpPrimNormal (SimpApplied PrimEmbedBYTES [a])) (SimpPrimNormal (SimpApplied PrimEmbedBYTES [b]))
  = SimpPrimNormal (SimpApplied PrimEmbedBYTES [primAddBYTES a b])
primAddBytes (SimpPrimNormal (SimpApplied PrimEmbedBYTES [SimpPrimNormal (SimpApplied PrimZeroBYTES [])])) b = b
primAddBytes a (SimpPrimNormal (SimpApplied PrimEmbedBYTES [SimpPrimNormal (SimpApplied PrimZeroBYTES [])])) = a
primAddBytes a@(Glued a') b = Glued (LazyPrimNormal (LazyApplied PrimAddBytes [a, b] (primAddBytes (simplified a') b)))
primAddBytes a b@(Glued b') = Glued (LazyPrimNormal (LazyApplied PrimAddBytes [a, b] (primAddBytes a (simplified b'))))
primAddBytes a b = SimpPrimNormal (SimpApplied PrimAddBytes [a, b])

public export
Eval (Term Value) (PrimitiveApplied k Syntax h) (Term Value) where
  eval env (($$) {r = PrimIrreducible} {k = PrimNorm} p sp) = SimpPrimNormal (SimpApplied p (eval env sp))
  eval env (($$) {r = PrimIrreducible} {k = PrimNeu} p sp) = SimpApps (PrimNeutral (SimpApplied p (eval env sp)) $$ [])
  eval env (PrimAddBYTES $$ [a, b]) = primAddBYTES (eval env a) (eval env b)
  eval env (PrimAddBytes $$ [a, b]) = primAddBytes (eval env a) (eval env b)
