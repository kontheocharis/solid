module Syntax

import Utils
import Context

record MetaVar where
  name : Name

data Stage = Obj | Mta

data Reducible : Stage -> Type where
  RedCallable : Reducible s
  RedLazy : Reducible s
  Irred : Reducible s

data Domain = Syntax | Value

data EvalMode : Domain -> Type where
  NA : EvalMode Syntax
  Normalised : EvalMode Value
  Simplified : EvalMode Value

data Term : Domain -> Ctx -> Type

Eval (Term Value) (Term Syntax) (Term Value)

data PrimitiveClass = PrimNeu | PrimNorm
data Primitive : PrimitiveClass -> Arity -> Type

data Binder : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  BindLam : Binder s RedCallable d ns
  BindLet : Term d ns -> Binder s RedLazy d ns
  BindLetIrr : Term d ns -> Binder Obj RedLazy d ns
  BindPiObj : (ba : Term d ns) -> (bb : Term d ns) -> (a : Term d ns) -> Binder Obj Irred d ns
  BindPiMta : (a : Term d ns) -> Binder Mta Irred d ns

Eval over (Term d) (Term d') => Eval over (Binder md r d) (Binder md r d') where
  eval _ BindLam = BindLam
  eval env (BindLet t) = BindLet (eval env t)
  eval env (BindLetIrr t) = BindLetIrr (eval env t)
  eval env (BindPiObj ba bb a) = BindPiObj (eval env ba) (eval env bb) (eval env a)
  eval env (BindPiMta a) = BindPiMta (eval env a)

data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable Value ns
  Index : Idx ns -> Variable Syntax ns

Eval (Term Value) (Variable Syntax) (Term Value) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

data Applied : (Arity -> Type) -> Domain -> Ctx -> Type where
  ($$) : k as -> Spine as (Term d) ns -> Applied k d ns

Eval (Term Value) (Applied (Primitive k) Syntax) (Term Value)

export infixr 5 $$

data Body : Domain -> Name -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term Value) ms -> Term Syntax (ms :< n) -> Body Value n ns

Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

data Thunk : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  Bound : (s : Stage) -> {0 r : Reducible s}
      -> (n : Name) -> Binder s r d ns -> Body d n ns -> Thunk s r d ns

callThunk : Thunk s RedCallable Value ns -> Term Value ns -> Term Value ns
callThunk (Bound s n BindLam (Closure env body)) arg = eval (env :< arg) body

forceThunk : Thunk s RedLazy Value ns -> Term Value ns
forceThunk (Bound s n (BindLet v) (Closure env body)) = eval (env :< v) body
forceThunk (Bound Obj n (BindLetIrr v) (Closure env body)) = eval (env :< v) body

Eval (Term Value) (Thunk s r Syntax) (Thunk s r Value) where
  eval env (Bound s n bind body) = Bound s n (eval env bind) (eval env body)

data Head : (d : Domain) -> EvalMode d -> Ctx -> Type where
  SynVar : Variable Syntax ns -> Head Syntax NA ns
  ValVar : Variable Value ns -> Head Value Simplified ns
  SynMeta : MetaVar -> Head Syntax NA ns
  ValMeta : MetaVar -> Head Value Simplified ns
  SynThunk : (s : Stage) -> (r : Reducible s) -> Thunk s r Syntax ns -> Head Syntax NA ns
  ObjCallable : Thunk Obj RedCallable Value ns -> Head Value Normalised ns
  ObjLazy : Thunk Obj RedLazy Value ns -> Head Value Normalised ns
  PrimNeutral : Applied (Primitive PrimNeu) d ns -> Head d e ns

0 HeadApplied : (d : Domain) -> EvalMode d -> Ctx -> Type
HeadApplied d e ns = Applied (\_ => Head d e ns) d ns

data Term where
  SynApps : HeadApplied Syntax NA ns -> Term Syntax ns
  GluedApps : HeadApplied Value Normalised ns -> Lazy (Term Value ns) -> Term Value ns
  SimpApps : HeadApplied Value Simplified ns -> Term Value ns
  MtaCallable : Thunk Mta RedCallable d ns -> Term d ns
  SimpObjCallable : Thunk Obj RedCallable Value ns -> Term Value ns
  IrredThunk : Thunk s Irred d ns -> Term d ns
  PrimNormal : Applied (Primitive PrimNorm) d ns -> Term d ns

apps : Term Value ns -> Spine as (Term Value) ns -> Term Value ns
apps (GluedApps (v $$ sp) gl) sp' = GluedApps (v $$ sp ++ sp') (apps gl sp')
apps (SimpApps (v $$ sp)) sp' = SimpApps (v $$ sp ++ sp')
apps (MtaCallable t) [] = MtaCallable t
apps (MtaCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (IrredThunk _) _ = error "impossible"
apps (PrimNormal _) _ = error "impossible"

Eval (Term Value) (Head Syntax NA) (Term Value) where
  eval env (SynVar v) = eval env v
  eval env (SynMeta v) = SimpApps (ValMeta v $$ [])
  eval env (SynThunk s Irred t) = IrredThunk {s = s} (eval env t)
  eval env (SynThunk Obj RedCallable t) = GluedApps (ObjCallable (eval env t) $$ []) (SimpObjCallable (eval env t))
  eval env (SynThunk Obj RedLazy t) = GluedApps (ObjLazy (eval env t) $$ []) (forceThunk {s = Obj} (eval env t))
  eval env (SynThunk Mta RedCallable t) = MtaCallable (eval env t)
  eval env (SynThunk Mta RedLazy t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

Eval (Term Value) (Term Syntax) (Term Value) where
  eval env (SynApps (($$) {as = as} h sp)) = apps {as = as} (eval env h) (eval env sp)
  eval env (MtaCallable t) = MtaCallable (eval env t)
  eval env (IrredThunk {s = s} t) = IrredThunk {s = s} (eval env t)
  eval env (PrimNormal prim) = eval env prim

0 Tm : Ctx -> Type
Tm = Term Syntax

0 Ty : Ctx -> Type
Ty = Tm

0 Val : Ctx -> Type
Val = Term Value

0 ValTy : Ctx -> Type
ValTy = Val

0 Env : Ctx -> Ctx -> Type
Env ms ns = Sub ms Val ns

var : (n : String) -> {auto prf : In n ns} -> Tm ns
var n {prf = prf} = SynApps (SynVar (Index (idx @{prf})) $$ [])

varApp : (n : String) -> {auto prf : In n ns} -> Name -> Term Syntax ns -> Tm ns
varApp n {prf = prf} a v = SynApps (SynVar (Index (idx @{prf})) $$ ((::) {a = a} v []))

-- foo : Tm [< (Explicit, "a"), (Explicit, "b"), (Explicit, "c")]
-- foo = var "c"

data Primitive where
  PrimTYPE : Primitive PrimNorm []
  PrimBYTES : Primitive PrimNorm []
  PrimBytes : Primitive PrimNorm []
  PrimEmbedBYTES : Primitive PrimNorm [(Explicit, "staticBytes")]
  PrimUnsized : Primitive PrimNorm [(Explicit, "bytes")]

TYPE : Term d ns
TYPE = PrimNormal (PrimTYPE $$ [])

BYTES : Term d ns
BYTES = PrimNormal (PrimBYTES $$ [])

Bytes : Term d ns
Bytes = PrimNormal (PrimBytes $$ [])

Unsized : Term d ns -> Term d ns
Unsized b = PrimNormal (PrimUnsized $$ [b])

EmbedBYTES : Term d ns -> Term d ns
EmbedBYTES b = PrimNormal (PrimEmbedBYTES $$ [b])

Sized : Term d ns -> Term d ns
Sized b = Unsized (EmbedBYTES b)



-- Tm = Term Idx (\n, ns => Tm (ns :< n))
-- Val = Term Idx Closure

-- (Eval over src dest) => Eval over (Binder s n src) (Binder s n dest) where
--   eval _ Lam = Lam
--   eval env (Let x y) = Let (eval env x) (eval env y)
--   eval env (LetIrr x y) = LetIrr (eval env x) (eval env y)
--   eval env (PiObj a b c) = PiObj (eval env a) (eval env b) (eval env c)
--   eval env (PiMta a) = PiMta (eval env a)
