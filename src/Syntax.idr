module Syntax

import Context

record MetaVar where
  name : Name

data Stage = Obj | Mta

data Reducible : Stage -> Type where
  RedLazy : Reducible s
  Red : Reducible s
  Irr : Reducible s

data IsStaged = Staged | Unstaged

data Domain = Syntax | Value IsStaged

data Term : Domain -> Ctx -> Type

data PrimitiveClass = PrimNeu | PrimNorm
data Primitive : PrimitiveClass -> Arity -> Type

data Binder : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  BindLam : Binder s Red d ns
  BindLet : Term d ns -> Binder s RedLazy d ns
  BindLetIrr : Term d ns -> Binder Obj RedLazy d ns
  BindPiObj : (ba : Term d ns) -> (bb : Term d ns) -> (a : Term d ns) -> Binder Obj Irr d ns
  BindPiMta : (a : Term d ns) -> Binder Mta Irr d ns

data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable (Value is) ns
  Index : Idx ns -> Variable Syntax ns

data Applied : (Arity -> Type) -> Domain -> Ctx -> Type where
  ($$) : k as -> Spine as (Term d) ns -> Applied k d ns

export infixr 5 $$

data Body : Domain -> Ctx -> Name -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax ns n
  Closure : Sub ns (Term (Value is)) ms -> Term Syntax (ms :< n) -> Body (Value is) ns n

data Thunk : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  Bound : (s : Stage) -> {0 r : Reducible s}
      -> (n : Name) -> Binder s r d ns -> Body d ns n -> Thunk s r d ns

data Head : Domain -> Ctx -> Type where
  Var : Variable d ns -> Head d ns
  Meta : MetaVar -> Head d ns
  SynRedex : Thunk s r Syntax ns -> Head Syntax ns
  ObjRedex : Thunk Obj Red (Value is) ns -> Head (Value is) ns
  ObjLazy : Thunk Obj RedLazy (Value is) ns -> Head (Value is) ns
  MtaLazy : Thunk Mta RedLazy (Value Unstaged) ns -> Head (Value Unstaged) ns
  PrimNeutral : Applied (Primitive PrimNeu) d ns -> Head d ns

data Term where
  Apps : Applied (\_ => Head d ns) d ns -> Term d ns
  Former : Thunk s Irr d ns -> Term d ns
  PrimNormal : Applied (Primitive PrimNorm) d ns -> Term d ns

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
