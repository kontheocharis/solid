module Evaluation

import Utils
import Context
import Syntax

%default covering -- won't bother with the totality checker here

-- Terms can be evalued and quoted (given later)
public export
0 EvalTm : Type
EvalTm = Eval (Term Value) (Term Syntax) (Term Value)

public export
0 ThinVal : Type
ThinVal = Thin (Term Value)

public export
0 QuoteVal : Type
QuoteVal = Quote (Term Value) (Term Syntax)

-- We will give the reduction rules of primitives separately
public export
0 EvalPrim : Type
EvalPrim = forall k . Eval (Term Value) (Applied (Primitive k) Syntax) (Term Value)

-- Evaluation and quoting for all the syntax:

-- Every callable thunk can be applied to a term.
public export
callThunk : EvalTm => Thunk s Callable Value ns -> Term Value ns -> Term Value ns
callThunk (Bound s n BindLam (Closure env body)) arg = eval (env :< arg) body

-- Every unforced thunk can be forced.
public export
forceThunk : EvalTm => Thunk s Unforced Value ns -> Term Value ns
forceThunk (Bound s n (BindLet v) (Closure env body)) = eval (env :< v) body

public export
QuoteVal => Quote (Applied f Value) (Applied f Syntax) where
  quote s (h $$ sp) = h $$ quote s sp

public export
ThinVal => Thin (Applied f Value) where
  thin e (h $$ sp) = h $$ thin e sp

public export
Eval over (Term d) (Term d') => Eval over (Binder md r d) (Binder md r d') where
  eval env b = mapBinder (eval env) b

public export
Quote (Term d) (Term d') => Quote (Binder md r d) (Binder md r d') where
  quote s b = mapBinder (quote s) b

public export
ThinVal => Thin (Binder md r Value) where
  thin e b = mapBinder (thin e) b

public export
Eval (Term Value) (Variable Syntax) (Term Value) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

public export
Quote (Variable Value) (Variable Syntax) where
  quote s (Level l) = Index (quote s l)

public export
(ThinVal) => Thin (Variable Value) where
  thin s (Level l) = Level (thin s l)

public export
ThinVal => Vars (Term Value) where
  here s = SimpApps (ValVar (Level (lastLvl s)) $$ [])

public export
Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

public export
(ThinVal, QuoteVal, EvalTm) => Quote (Body Value n) (Body Syntax n) where
  quote s (Closure env t) = Delayed (quote {val = Term Value} (SS s) (eval (lift s env) t))

public export
ThinVal => Thin (Body Value n) where
  thin e (Closure env t) = Closure (env . e) t

public export
EvalTm => Eval (Term Value) (Thunk s r Syntax) (Thunk s r Value) where
  eval env (Bound s n bind body) = Bound s n (eval env bind) (eval env body)

public export
(ThinVal, QuoteVal, EvalTm) => Quote (Thunk s r Value) (Thunk s r Syntax) where
  quote s (Bound s' n bind body) = Bound s' n (quote s bind) (quote s body)

public export
ThinVal => Thin (Thunk s r Value) where
  thin s (Bound s' n bind body) = Bound s' n (thin s bind) (thin s body)

-- Helper to apply a value to a spine.
--
-- This is the only place where it could crash if there is a bug, because
-- the syntax is not well-typed (only well-scoped).
public export
apps : EvalTm => Term Value ns -> Spine as (Term Value) ns -> Term Value ns
apps (GluedApps (v $$ sp) gl) sp' = GluedApps (v $$ sp ++ sp') (apps gl sp')
apps (SimpApps (v $$ sp)) sp' = SimpApps (v $$ sp ++ sp')
apps (MtaCallable t) [] = MtaCallable t
apps (MtaCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (RigidThunk _) _ = error "impossible"
apps (PrimNormal _) _ = error "impossible"

public export
(EvalTm, EvalPrim) => Eval (Term Value) (Head Syntax NA) (Term Value) where
  eval env (SynVar v) = eval env v
  eval env (SynMeta v) = SimpApps (ValMeta v $$ [])
  eval env (SynThunk s Rigid t) = RigidThunk {s = s} (eval env t)
  eval env (SynThunk Obj Callable t) = GluedApps (ObjCallable (eval env t) $$ []) (SimpObjCallable (eval env t))
  eval env (SynThunk Obj Unforced t) = GluedApps (ObjLazy (eval env t) $$ []) (forceThunk {s = Obj} (eval env t))
  eval env (SynThunk Mta Callable t) = MtaCallable (eval env t)
  eval env (SynThunk Mta Unforced t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

public export
(ThinVal, QuoteVal, EvalTm) => Quote (Head Value hk) (Head Syntax NA) where
  quote s (ValVar v) = SynVar (quote s v)
  quote s (ValMeta m) = SynMeta m
  quote s (ObjCallable t) = SynThunk Obj Callable (quote s t)
  quote s (ObjLazy t) = SynThunk Obj Unforced (quote s t)
  quote s (PrimNeutral p) = PrimNeutral (quote s p)

public export
ThinVal => Thin (Head Value hk) where
  thin s (ValVar v) = ValVar (thin s v)
  thin s (ValMeta m) = ValMeta m
  thin s (ObjCallable t) = ObjCallable (thin s t)
  thin s (ObjLazy t) = ObjLazy (thin s t)
  thin s (PrimNeutral p) = PrimNeutral (thin s p)

public export
(ThinVal, QuoteVal, EvalTm) => Quote (HeadApplied Value hk) (HeadApplied Syntax NA) where
  quote s (($$) {as = as} h sp) = ($$) {as = as} (quote s h) (quote s sp)

public export
ThinVal => Thin (HeadApplied Value hk) where
  thin e (h $$ sp) = thin e h $$ thin e sp

public export
Thin (Term Value) where
  thin e (GluedApps a f) = GluedApps (thin e a) (thin e f)
  thin e (SimpApps a) = SimpApps (thin e a)
  thin e (MtaCallable c) = MtaCallable (thin e c)
  thin e (SimpObjCallable c) = SimpObjCallable (thin e c)
  thin e (RigidThunk c) = RigidThunk (thin e c)
  thin e (PrimNormal p) = PrimNormal (thin e p)

public export
EvalPrim => Eval (Term Value) (Term Syntax) (Term Value) where
  eval env (SynApps (($$) {as = as} h sp)) = apps {as = as} (eval env h) (eval env sp)
  eval env (RigidThunk {s = s} t) = RigidThunk {s = s} (eval env t)
  eval env (PrimNormal prim) = eval env prim

public export
EvalPrim => Quote (Term Value) (Term Syntax) where
  quote s (GluedApps a _) = SynApps (quote s a)
  quote s (SimpApps a) = SynApps (quote s a)
  quote s (MtaCallable c) = SynApps (SynThunk Mta Callable (quote s c) $$ [])
  quote s (SimpObjCallable c) = SynApps (SynThunk Obj Callable (quote s c) $$ [])
  quote s (RigidThunk {s = s'} c) = RigidThunk {s = s'} (quote s c)
  quote s (PrimNormal p) = PrimNormal (quote s p)
