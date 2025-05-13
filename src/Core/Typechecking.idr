module Core.Typechecking

import Core.Syntax
import Core.Base
import Core.Evaluation
import Core.Metavariables

%default covering

data TcMode : Type where
  Check : TcMode
  Infer : TcMode

record Context (ns : Ctx) where
  constructor MkContext
  con : Con ValTy ns
  defs : Sub ns Val ns
  stages : SnocList Stage
  size : Size ns

record ExprAt (s : Stage) (d : Domain) (ns : Ctx) where
  constructor MkExprAny
  tm : Term d ns
  ty : ValTy ns

record Expr (d : Domain) (ns : Ctx) where
  constructor MkExpr
  tm : Term d ns
  ty : ValTy ns
  stage : Stage

record Annot (ns : Ctx) where
  constructor MkAnnot
  ty : ValTy ns
  stage : Stage

define : (n : Ident) -> Expr Value ns -> Context ns -> Context (ns :< n)
define n rhs (MkContext con defs stages size) =
  MkContext (con :< rhs.ty) (defs . Drop Id :< wk rhs.tm) (stages :< rhs.stage) (SS size)

bind : (n : Ident) -> Annot ns -> Context ns -> Context (ns :< n)
bind n annot (MkContext con defs stages size) =
  MkContext (con :< annot.ty) (defs . Drop Id :< varLvl (lastLvl size)) (stages :< annot.stage) (SS size)

interface (Monad m) => HasTc m where
  metas : HasMetas (const m)

resolve : HasTc m => Val ns -> m (Val ns)
resolve x = resolveMetas {sm = SolvingAllowed} @{metas} x

data Tc : (0 m : _) -> HasTc m => (md : TcMode) -> Ctx -> Type where
  InCheck : HasTc m => (Context ns -> Annot ns -> m (Tm ns)) -> Tc m Check ns
  InInfer : HasTc m => (Context ns -> m (Expr Syntax ns)) -> Tc m Infer ns
  InInferAt : HasTc m => (Context ns -> (s : Stage) -> m (ExprAt s Syntax ns)) -> Tc m Infer ns

insertAll : (HasTc m) => Context ns -> m (Expr Syntax ns) -> m (Expr Syntax ns)

insert : (HasTc m) => Context ns -> m (Expr Syntax ns) -> m (Expr Syntax ns)

insertAt : (HasTc m) => Context ns -> (s : Stage) -> m (ExprAt s Syntax ns) -> m (ExprAt s Syntax ns)

insertUntil : (HasTc m) => Context ns -> Name -> m (Expr Syntax ns) -> m (Expr Syntax ns)

tryAdjustStage : (HasTc m) => Context ns -> Expr Syntax ns -> (s : Stage) -> m (Maybe (ExprAt s Syntax ns))

adjustStage : (HasTc m) => Context ns -> Expr Syntax ns -> (s : Stage) -> m (ExprAt s Syntax ns)

coerce : (HasTc m) => Expr Syntax ns -> Annot ns -> m (Tm ns)

check : HasTc m => Tc m md ns -> Tc m Check ns
check (InInferAt f)
  = InCheck $ \ctx, annot => (.tm) <$> (insertAt ctx annot.stage $ f ctx annot.stage)
check (InInfer f)
  = InCheck $ \ctx, annot => (.tm) <$> (insert ctx $ f ctx)
check (InCheck f) = InCheck f

lamCheck : HasTc m
  => (n : Ident)
  -> (ty : Maybe (Tc m md ns))
  -> (body : Tc m md (ns :< n))
  -> Tc m Check ns
lamCheck n bindTy body = InCheck $ \ctx, (MkAnnot ty stage) => do
  ty' <- resolve ty
  ?fa
  -- case ty' of
  --   RigidBinding a (Bound _ ) => ?fafafa

-- tcLam : HasTc m => (s : Stage) -> (n : Ident) -> Tc m md (ns :< n) -> Tc m Check ns
-- tcLam st n body = InCheck $ \ctx, ty => ?fa
