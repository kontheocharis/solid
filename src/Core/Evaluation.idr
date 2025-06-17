-- Defining NbE for the core language
module Core.Evaluation

import Data.Singleton
import Utils
import Common
import Core.Base
import Core.Primitives
import Core.Syntax

%default covering -- won't bother with the totality checker here

-- We will give the reduction rules of primitives separately
public export
0 EvalPrims : Type
EvalPrims = forall k, e . Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value)

-- Terms can be evalued and quoted (given later)
public export
EvalPrims => Eval (Term Value) (Term Syntax) (Term Value)

public export
EvalPrims => Quote (Term Value) (Term Syntax)

public export
Weak (Term Value)

-- Evaluation and quoting for all the syntax:

-- Every callable binding value can be applied to a term.
public export
callBinding : EvalPrims => Binding s Callable Value ns -> Term Value ns -> Term Value ns
callBinding (Bound _ (BindObjLam _ _ _) (Closure env body)) arg = eval (env :< arg) body
callBinding (Bound _ (BindMtaLam _) (Closure env body)) arg = eval (env :< arg) body
callBinding (Bound s InternalLam (Closure env body)) arg = eval (env :< arg) body

-- Every thunk can be forced.
public export
forceThunk : EvalPrims => Binding s Thunk Value ns -> Term Value ns
forceThunk (Bound _ (BindObjLet _ _ _ v) (Closure env body)) = eval (env :< v) body
forceThunk (Bound _ (BindMtaLet _ _ v) (Closure env body)) = eval (env :< v) body

public export
EvalPrims => Quote (PrimitiveApplied k Value e) (PrimitiveApplied k Syntax NA) where
  quote (SimpApplied h sp) = h $$ quote sp
  quote (LazyApplied h sp _) = h $$ quote sp

public export
Weak (PrimitiveApplied k Value e) where
  weak e (SimpApplied h sp) = SimpApplied h (weak e sp)
  weak e (LazyApplied h sp gl) = LazyApplied h (weak e sp) (weak e gl)

public export
Eval over (Term d) (Term d') => Eval over (Binder md r d n) (Binder md r d' n) where
  eval env b = mapBinder (eval env) b

public export
Quote (Term d) (Term d') => Quote (Binder md r d n) (Binder md r d' n) where
  quote b = mapBinder (quote) b

public export
Weak (Binder md r Value n) where
  weak e b = mapBinder (weak e) b

public export
Eval (Term Value) (Variable Syntax) (Term Value) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

public export
Quote (Variable Value) (Variable Syntax) where
  quote (Level l) = Index (quote l)

public export
Weak (Variable Value) where
  weak s (Level l) = Level (weak s l)

public export
Vars (Term Value) where
  here {sz = s} = SimpApps (ValVar (Level (lastLvl s)) $$ [])

public export
Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

public export
EvalPrims => Quote (Body Value n) (Body Syntax n) where
  quote (Closure env t) = Delayed (quote {val = Term Value} (eval (lift env) t))

public export
Weak (Body Value n) where
  weak e (Closure env t) = Closure (env . e) t

public export
EvalPrims => Eval (Term Value) (Binding md r Syntax) (Binding md r Value) where
  eval env (Bound {n = n} md bind body) = Bound {n = n} md (eval env bind) (eval env body)

public export
EvalPrims => Quote (Binding md r Value) (Binding md r Syntax) where
  quote (Bound {n = n} md bind body) = Bound {n = n} md (quote bind) (quote body)

public export
Weak (Binding md r Value) where
  weak s (Bound {n = n} md bind body) = Bound {n = n} md (weak s bind) (weak s body)

-- Helper to apply a value to a spine.
--
-- This is the only place where it could crash if there is a bug, because
-- the syntax is not well-typed (only well-scoped).
public export
apps : EvalPrims => Term Value ns -> Spine ar (Term Value) ns -> Term Value ns
apps (Glued (LazyApps (v $$ sp) gl)) sp' = Glued (LazyApps (v $$ sp ++ sp') (apps gl sp'))
apps (SimpApps (v $$ sp)) sp' = SimpApps (v $$ sp ++ sp')
apps (MtaCallable t) [] = MtaCallable t
apps (MtaCallable t) ((_, x) :: sp') = apps (callBinding t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) ((_, x) :: sp') = apps (callBinding t x) sp'
apps (RigidBinding _ _) _ = error "impossible"
apps (SimpPrimNormal _) sp' = error "impossible"
apps (Glued (LazyPrimNormal _)) sp' = error "impossible"

public export
EvalPrims => Eval (Term Value) (Head Syntax NA) (Term Value) where
  eval env (SynVar v) = eval env v
  eval env (SynMeta v) = SimpApps (ValMeta v $$ [])
  eval env (SynBinding md Rigid t) = RigidBinding md (eval env t)
  eval env (SynBinding Obj Callable t) = Glued (LazyApps (ObjCallable (eval env t) $$ []) (SimpObjCallable (eval env t)))
  eval env (SynBinding Obj Thunk t) = Glued (LazyApps (ObjLazy (eval env t) $$ []) (forceThunk {s = Obj} (eval env t)))
  eval env (SynBinding Mta Callable t) = MtaCallable (eval env t)
  eval env (SynBinding Mta Thunk t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

public export
EvalPrims => Quote (Head Value hk) (Head Syntax NA) where
  quote (ValVar v) = SynVar (quote v)
  quote (ValMeta m) = SynMeta m
  quote (ValDef v) = SynVar (quote v)
  quote (ObjCallable t) = SynBinding Obj Callable (quote t)
  quote (ObjLazy t) = SynBinding Obj Thunk (quote t)
  quote (PrimNeutral p) = PrimNeutral {e = NA} (quote p)

public export
Weak (Head Value hk) where
  weak s (ValVar v) = ValVar (weak s v)
  weak s (ValMeta m) = ValMeta m
  weak s (ValDef v) = ValDef (weak s v)
  weak s (ObjCallable t) = ObjCallable (weak s t)
  weak s (ObjLazy t) = ObjLazy (weak s t)
  weak s (PrimNeutral p) = PrimNeutral (weak s p)

public export
EvalPrims => Eval (Term Value) (HeadApplied Syntax NA) (Term Value) where
  eval env (($$) {ar = ar} h sp) = apps {ar = ar} (eval env h) (eval env sp)

public export
EvalPrims => Quote (HeadApplied Value hk) (HeadApplied Syntax NA) where
  quote (($$) {ar = ar} h sp) = ($$) {ar = ar} (quote h) (quote sp)

public export
Weak (HeadApplied Value hk) where
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
EvalPrims => Eval (Term Value) (Term Syntax) (Term Value) where
  eval env (SynApps ha) = eval env ha
  eval env (RigidBinding md t) = RigidBinding md (eval env t)
  eval env (SynPrimNormal prim) = eval env prim

public export
EvalPrims => Quote (Term Value) (Term Syntax) where
  quote (Glued (LazyApps a _)) = SynApps (quote a)
  quote (Glued (LazyPrimNormal a)) = SynPrimNormal (quote a)
  quote (SimpApps a) = SynApps (quote a)
  quote (MtaCallable c) = SynApps (SynBinding Mta Callable (quote c) $$ [])
  quote (SimpObjCallable c) = SynApps (SynBinding Obj Callable (quote c) $$ [])
  quote (RigidBinding md c) = RigidBinding md (quote c)
  quote (SimpPrimNormal p) = SynPrimNormal (quote p)
  
public export
EvalPrims => WeakSized (Term Syntax) where
  weakS e t = quote {val = Term Value} (weak e (eval id t))

public export
EvalPrims => Vars (Term Syntax) where
  here = SynApps ((SynVar (Index here)) $$ [])