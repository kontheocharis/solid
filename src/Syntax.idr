module Syntax

import Utils
import Context

record MetaVar where
  name : Name

data Stage = Obj | Mta

data Reducible : Stage -> Type where
  RedCall : Reducible s
  RedLazy : Reducible s
  Irred : Reducible s

data IsStaged = Staged | Unstaged

data Domain = Syntax | Value IsStaged

data Term : Domain -> Ctx -> Type

{is : IsStaged} -> Eval (Term (Value is)) (Term Syntax) (Term (Value is))

data PrimitiveClass = PrimNeu | PrimNorm
data Primitive : PrimitiveClass -> Arity -> Type

data Binder : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  BindLam : Binder s RedCall d ns
  BindLet : Term d ns -> Binder s RedLazy d ns
  BindLetIrr : Term d ns -> Binder Obj RedLazy d ns
  BindPiObj : (ba : Term d ns) -> (bb : Term d ns) -> (a : Term d ns) -> Binder Obj Irred d ns
  BindPiMta : (a : Term d ns) -> Binder Mta Irred d ns

Eval over (Term d) (Term d') => Eval over (Binder is r d) (Binder is r d') where
  eval _ BindLam = BindLam
  eval env (BindLet t) = BindLet (eval env t)
  eval env (BindLetIrr t) = BindLetIrr (eval env t)
  eval env (BindPiObj ba bb a) = BindPiObj (eval env ba) (eval env bb) (eval env a)
  eval env (BindPiMta a) = BindPiMta (eval env a)

data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable (Value is) ns
  Index : Idx ns -> Variable Syntax ns

Eval (Term (Value is)) (Variable Syntax) (Term (Value is)) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

data Applied : (Arity -> Type) -> Domain -> Ctx -> Type where
  ($$) : k as -> Spine as (Term d) ns -> Applied k d ns

Eval (Term (Value is)) (Applied (Primitive k) Syntax) (Term (Value is))

export infixr 5 $$

data Body : Domain -> Name -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term (Value is)) ms -> Term Syntax (ms :< n) -> Body (Value is) n ns

Eval (Term (Value is)) (Body Syntax n) (Body (Value is) n) where
  eval env (Delayed t) = Closure env t

data Thunk : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  Bound : (s : Stage) -> {0 r : Reducible s}
      -> (n : Name) -> Binder s r d ns -> Body d n ns -> Thunk s r d ns

callThunk : {is : IsStaged} -> Thunk s RedCall (Value is) ns -> Term (Value is) ns -> Term (Value is) ns
callThunk (Bound s n BindLam (Closure env body)) arg = eval (env :< arg) body

forceThunk : {is : IsStaged} -> Thunk s RedLazy (Value is) ns -> Term (Value is) ns
forceThunk (Bound s n (BindLet v) (Closure env body)) = eval (env :< v) body
forceThunk (Bound Obj n (BindLetIrr v) (Closure env body)) = eval (env :< v) body

{is : IsStaged} -> Eval (Term (Value is)) (Thunk s r Syntax) (Thunk s r (Value is)) where
  eval env (Bound s n bind body) = Bound s n (eval env bind) (eval env body)

data Head : Domain -> Ctx -> Type where
  Var : Variable d ns -> Head d ns
  Meta : MetaVar -> Head d ns
  SynThunk : (s : Stage) -> (r : Reducible s) -> Thunk s r Syntax ns -> Head Syntax ns
  ObjCall : Thunk Obj RedCall (Value is) ns -> Head (Value is) ns
  ObjLazy : Thunk Obj RedLazy (Value is) ns -> Head (Value is) ns
  MtaLazy : Thunk Mta RedLazy (Value Unstaged) ns -> Head (Value Unstaged) ns
  PrimNeutral : Applied (Primitive PrimNeu) d ns -> Head d ns

data Term where
  Apps : Applied (\_ => Head d ns) d ns -> Term d ns
  MtaCall : Thunk Mta RedCall d ns -> Term d ns
  IrredThunk : Thunk s Irred d ns -> Term d ns
  PrimNormal : Applied (Primitive PrimNorm) d ns -> Term d ns

apps : {is : IsStaged} -> Term (Value is) ns -> Spine as (Term (Value is)) ns -> Term (Value is) ns
apps (Apps (v $$ sp)) sp' = Apps (v $$ sp ++ sp')
apps (MtaCall t) [] = MtaCall t
apps (MtaCall t) (x :: sp') = apps (callThunk t x) sp'
apps (IrredThunk _) _ = error "impossible"
apps (PrimNormal _) _ = error "impossible"

{is : IsStaged} -> Eval (Term (Value is)) (Term Syntax) (Term (Value is))

{is : IsStaged} -> Eval (Term (Value is)) (Head Syntax) (Term (Value is)) where
  eval env (Var v) = eval env v
  eval env (Meta v) = Apps (Meta v $$ [])
  eval env (SynThunk s Irred t) = IrredThunk {s = s} (eval env t)
  eval env (SynThunk Obj RedCall t) = Apps (ObjCall (eval env t) $$ [])
  eval env (SynThunk Obj RedLazy t) = Apps (ObjLazy (eval env t) $$ [])
  eval env (SynThunk Mta RedCall t) = MtaCall (eval env t)
  eval {is = Unstaged} env (SynThunk Mta RedLazy t) = Apps (MtaLazy (eval env t) $$ [])
  eval {is = Staged} env (SynThunk Mta RedLazy t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

{is : IsStaged} -> Eval (Term (Value is)) (Term Syntax) (Term (Value is)) where
  eval env (Apps (($$) {as = as} h sp)) = apps {as = as} (eval env h) (eval env sp)
  eval env (MtaCall t) = MtaCall (eval env t)
  eval env (IrredThunk {s = s} t) = IrredThunk {s = s} (eval env t)
  eval env (PrimNormal prim) = eval env prim

0 Tm : Ctx -> Type
Tm = Term Syntax

0 Ty : Ctx -> Type
Ty = Tm

0 Val : Ctx -> Type
Val = Term (Value Unstaged)

0 ValTy : Ctx -> Type
ValTy = Val

0 StagedVal : Ctx -> Type
StagedVal = Term (Value Staged)

0 Env : Ctx -> Ctx -> Type
Env ms ns = Sub ms Val ns

0 StagedEnv : Ctx -> Ctx -> Type
StagedEnv ms ns = Sub ms StagedVal ns

var : (n : String) -> {auto prf : In n ns} -> Tm ns
var n {prf = prf} = Apps (Var (Index (idx @{prf})) $$ [])

varApp : (n : String) -> {auto prf : In n ns} -> Name -> Term Syntax ns -> Tm ns
varApp n {prf = prf} a v = Apps (Var (Index (idx @{prf})) $$ ((::) {a = a} v []))

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
