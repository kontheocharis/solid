-- Defining NbE for the core language
module Core.Evaluation

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
  quote s (SimpApplied h sp) = h $$ quote s sp
  quote s (LazyApplied h sp _) = h $$ quote s sp

public export
Weak (PrimitiveApplied k Value e) where
  weak e (SimpApplied h sp) = SimpApplied h (weak e sp)
  weak e (LazyApplied h sp gl) = LazyApplied h (weak e sp) (weak e gl)

public export
Eval over (Term d) (Term d') => Eval over (Binder md r d n) (Binder md r d' n) where
  eval env b = mapBinder (eval env) b

public export
Quote (Term d) (Term d') => Quote (Binder md r d n) (Binder md r d' n) where
  quote s b = mapBinder (quote s) b

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
  quote s (Level l) = Index (quote s l)

public export
Weak (Variable Value) where
  weak s (Level l) = Level (weak s l)

public export
Vars (Term Value) where
  here s = SimpApps (ValVar (Level (lastLvl s)) $$ [])

public export
Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

public export
EvalPrims => Quote (Body Value n) (Body Syntax n) where
  quote s (Closure env t) = Delayed (quote {val = Term Value} (SS s) (eval (lift s env) t))

public export
Weak (Body Value n) where
  weak e (Closure env t) = Closure (env . e) t

public export
EvalPrims => Eval (Term Value) (Binding md r Syntax) (Binding md r Value) where
  eval env (Bound {n = n} md bind body) = Bound {n = n} md (eval env bind) (eval env body)

public export
EvalPrims => Quote (Binding md r Value) (Binding md r Syntax) where
  quote s (Bound {n = n} md bind body) = Bound {n = n} md (quote s bind) (quote s body)

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
apps (MtaCallable t) (x :: sp') = apps (callBinding t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) (x :: sp') = apps (callBinding t x) sp'
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
  quote s (ValVar v) = SynVar (quote s v)
  quote s (ValMeta m) = SynMeta m
  quote s (ValDef v) = SynVar (quote s v)
  quote s (ObjCallable t) = SynBinding Obj Callable (quote s t)
  quote s (ObjLazy t) = SynBinding Obj Thunk (quote s t)
  quote s (PrimNeutral p) = PrimNeutral {e = NA} (quote s p)

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
  quote s (($$) {ar = ar} h sp) = ($$) {ar = ar} (quote s h) (quote s sp)

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
  quote s (Glued (LazyApps a _)) = SynApps (quote s a)
  quote s (Glued (LazyPrimNormal a)) = SynPrimNormal (quote s a)
  quote s (SimpApps a) = SynApps (quote s a)
  quote s (MtaCallable c) = SynApps (SynBinding Mta Callable (quote s c) $$ [])
  quote s (SimpObjCallable c) = SynApps (SynBinding Obj Callable (quote s c) $$ [])
  quote s (RigidBinding md c) = RigidBinding md (quote s c)
  quote s (SimpPrimNormal p) = SynPrimNormal (quote s p)
  
public export
EvalPrims => WeakSized (Term Syntax) where
  weakS src dest e t = quote {val = Term Value} src (weak e (eval (id dest) t))
  
public export
EvalPrims => WeakSized Annot where
  weakS src dest e (MkAnnot t a s) = MkAnnot (weakS src dest e t) (weakS src dest e a) s

public export
EvalPrims => WeakSized (AnnotAt s) where
  weakS src dest e (MkAnnotAt t a) = MkAnnotAt (weakS src dest e t) (weakS src dest e a)

public export
EvalPrims => WeakSized Expr where
  weakS src dest e (MkExpr t a) = MkExpr (weakS src dest e t) (weakS src dest e a)

public export
EvalPrims => WeakSized (ExprAt s) where
  weakS src dest e (MkExprAt t a) = MkExprAt (weakS src dest e t) (weakS src dest e a)

