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

data Binder : (s : Stage) -> Domain -> Reducible s -> Ctx -> Type where
  --
  Lam : Binder s d Red ns
  -- ty, tm
  Let : Term d ns -> Term d ns -> Binder s d RedLazy ns
  -- ty, tm
  LetIrr : Term d ns -> Term d ns -> Binder Obj d RedLazy ns
  -- a, b, A
  PiObj : Term d ns -> Term d ns -> Term d ns -> Binder Obj d Irr ns
  -- A
  PiMta : Term d ns -> Binder Mta d Irr ns

data PrimitiveKind = PrimNeu | PrimNorm

data Primitive : Arity -> PrimitiveKind -> Type

data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable (Value is) ns
  Index : Idx ns -> Variable Syntax ns

data Head : Domain -> Ctx -> Type where
  Var : Variable d ns -> Head d ns
  Meta : MetaVar -> Head d ns
  SynRedex : (n : Name) -> Binder s Syntax r ns -> Head Syntax ns
  ObjRedex : (n : Name) -> Binder Obj (Value is) Red ns -> Head (Value is) ns
  MtaLazyRedex : (n : Name) -> Binder Mta (Value Unstaged) RedLazy ns -> Head (Value Unstaged) ns
  PrimNeutral : Primitive ks PrimNeu -> Spine ks (Term d) ns -> Head d ns

data Term where
  Apps : Head d ns -> Spine ks (Term d) ns -> Term d ns
  Bind : (s : Stage) -> (n : Name) -> Binder s d Irr ns -> Term d ns
  PrimNormal : Primitive ks PrimNorm -> Term d ns

data Body : Domain -> Name -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term (Value is)) ms -> Term Syntax (ms :< n) -> Body (Value is) n ns

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
