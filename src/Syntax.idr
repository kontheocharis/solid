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

data Binder : (s : Stage) -> Reducible s -> Arity -> Type where
  Lam : Binder s Red [(Implicit, "ty")]
  Let : Binder s RedLazy [(Explicit, "ty"), (Explicit, "tm")]
  LetIrr : Binder Obj RedLazy [(Explicit, "ty"), (Explicit, "tm")]
  PiObj : Binder Obj Irr [(Implicit, "bytesIn"), (Implicit, "bytesOut"), (Explicit, "ty")]
  PiMta : Binder Mta Irr [(Explicit, "ty")]

data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable (Value is) ns
  Index : Idx ns -> Variable Syntax ns

data Model : (Arity -> Type) -> Domain -> Ctx -> Type where
  Spined : k as -> Spine as (Term d) ns -> Model k d ns

data Body : Domain -> Name -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term (Value is)) ms -> Term Syntax (ms :< n) -> Body (Value is) n ns

data Thunk : (s : Stage) -> Reducible s -> Domain -> Ctx -> Type where
  Bound : (s : Stage) -> {0 r : Reducible s}
      -> (n : Name) -> Model (Binder s r) d ns -> Body d n ns -> Thunk s r d ns

data Head : Domain -> Ctx -> Type where
  Var : Variable d ns -> Head d ns
  Meta : MetaVar -> Head d ns
  SynRedex : Thunk s r Syntax ns -> Head Syntax ns
  ObjRedex : Thunk Obj Red (Value is) ns -> Head (Value is) ns
  MtaLazy : Thunk Mta RedLazy (Value Unstaged) ns -> Head (Value Unstaged) ns
  PrimNeutral : Model (Primitive PrimNeu) d ns -> Head d ns

data Term where
  Apps : Head d ns -> Spine ks (Term d) ns -> Term d ns
  Former : Thunk s Irr d ns -> Term d ns
  PrimNormal : Model (Primitive PrimNorm) d ns -> Term d ns

0 Tm : Ctx -> Type
Tm = Term Syntax

0 Val : Ctx -> Type
Val = Term (Value Unstaged)

0 StagedVal : Ctx -> Type
StagedVal = Term (Value Staged)

0 Env : Ctx -> Ctx -> Type
Env ms ns = Sub ms Val ns

0 StagedEnv : Ctx -> Ctx -> Type
StagedEnv ms ns = Sub ms StagedVal ns

var : (n : String) -> {auto prf : In n ns} -> Tm ns
var n {prf = prf} = Apps (Var (Index (idx @{prf}))) []

foo : Tm [< (Explicit, "a"), (Explicit, "b"), (Explicit, "c")]
foo = var "c"

-- data Term where
--   App : Head var delay ns -> Spine ks (Term var delay) ns -> Term var delay ns




-- Tm = Term Idx (\n, ns => Tm (ns :< n))
-- Val = Term Idx Closure

-- (Eval over src dest) => Eval over (Binder s n src) (Binder s n dest) where
--   eval _ Lam = Lam
--   eval env (Let x y) = Let (eval env x) (eval env y)
--   eval env (LetIrr x y) = LetIrr (eval env x) (eval env y)
--   eval env (PiObj a b c) = PiObj (eval env a) (eval env b) (eval env c)
--   eval env (PiMta a) = PiMta (eval env a)
