-- Typechecking combinators for the core language.
module Core.Typechecking

import Core.Syntax
import Core.Base
import Core.Evaluation
import Core.Metavariables

%default covering

-- Typechecking modes
data TcMode : Type where
  -- Check against a type, produce an elaborated term
  Check : TcMode
  -- Infer to produce an elaborated term and type
  Infer : TcMode
  -- Infer at a given stage, to produce an elaborated term and type
  InferAt : TcMode

-- Context for typechecking
record Context (ns : Ctx) where
  constructor MkContext
  -- The current context of types
  con : Con ValTy ns
  -- The definitions in the context
  --
  -- This is an endomorphism of `con`; bindings are mapped to their level, and
  -- definitions are mapped to their value.
  defs : Sub ns Val ns
  -- The stages of the definitions in the context
  stages : SnocList Stage
  -- The size of the context, for quick access
  size : Size ns

-- A typed expression at a given stage
record ExprAt (s : Stage) (d : Domain) (ns : Ctx) where
  constructor MkExprAt
  tm : Term d ns
  ty : ValTy ns

-- Version of ExprAt which also packages the stage
record Expr (d : Domain) (ns : Ctx) where
  constructor MkExpr
  tm : Term d ns
  ty : ValTy ns
  stage : Stage

-- An annotation is a type and a stage
record Annot (ns : Ctx) where
  constructor MkAnnot
  ty : ValTy ns
  stage : Stage

-- Add a definition to the context that eagerly evaluates to its value.
eagerDefine : (n : Ident) -> Expr Value ns -> Context ns -> Context (ns :< n)
eagerDefine n rhs (MkContext con defs stages size) =
  MkContext (con :< rhs.ty) (defs . Drop Id :< wk rhs.tm) (stages :< rhs.stage) (SS size)

-- Add a definition to the context that lazily evaluates to its value.
lazyDefine : (n : Ident) -> Expr Value ns -> Context ns -> Context (ns :< n)
lazyDefine n rhs (MkContext con defs stages size) =
  MkContext (con :< rhs.ty)
    (defs . Drop Id :< Glued (LazyApps (ValDef (Level (lastLvl size)) $$ []) (wk rhs.tm)))
    (stages :< rhs.stage)
    (SS size)

-- Add a binding with no value to the context.
bind : (n : Ident) -> Annot ns -> Context ns -> Context (ns :< n)
bind n annot (MkContext con defs stages size) =
  MkContext (con :< annot.ty) (defs . Drop Id :< varLvl (lastLvl size)) (stages :< annot.stage) (SS size)

-- Typechecking has access to metas
interface (Monad m) => HasTc m where
  -- Explicit instance of metas so that the resolution doesn't die..
  metas : HasMetas (const m)


-- This is the type over which we build the typechecking combinators.
--
-- `TcOp m md ns` is a typechecking operation in mode md.
--
-- It can be executed to produce an elaborated expression, depending on what `md` is.
0 TcOp : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcOp Check m ms = Annot ms -> m (Tm ms)
TcOp Infer m ms = m (Expr Syntax ms)
TcOp InferAt m ms = (s : Stage) -> m (ExprAt s Syntax ms)

-- Typechecking in a specific context
0 TcAt : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcAt md m ns = Context ns -> TcOp md m ns

-- Typechecking in any context
0 Tc : (md : TcMode) -> (0 m : Type -> Type) -> Type
Tc md m = forall ns . TcAt md m ns

-- Some useful shorthands

resolve : HasTc m => Val ns -> m (Val ns)
resolve x = resolveGlueAndMetas {sm = SolvingAllowed} @{metas} x

evaluate : Context ns -> Tm ns -> Val ns
evaluate ctx t = eval ctx.defs t

freshMetaVal : HasTc m => Context ns -> m (Val ns)

freshMeta : HasTc m => Context ns -> m (Tm ns)

-- Insert all lambdas implicit lambdas in a type-directed manner, without regard
-- for what the expression is.
insertAll : (HasTc m) => Context ns -> m (Expr Syntax ns) -> m (Expr Syntax ns)

-- Insert all lambdas implicit lambdas in a type-directed manner, unless the given expression is a
-- matching implicit lambda.
insert : (HasTc m) => Context ns -> m (Expr Syntax ns) -> m (Expr Syntax ns)

-- Stage-aware `insert`.
insertAt : (HasTc m) => Context ns -> (s : Stage) -> m (ExprAt s Syntax ns) -> m (ExprAt s Syntax ns)

-- Insert until a given name is reached.
insertUntil : (HasTc m) => Context ns -> Name -> m (Expr Syntax ns) -> m (Expr Syntax ns)

-- Try to adjust the stage of an expression.
tryAdjustStage : (HasTc m) => Context ns -> Expr Syntax ns -> (s : Stage) -> m (Maybe (ExprAt s Syntax ns))

-- Adjust the stage of an expression.
adjustStage : (HasTc m) => Context ns -> Expr Syntax ns -> (s : Stage) -> m (ExprAt s Syntax ns)

-- Coerce an expression to a given type.
coerce : (HasTc m) => Expr Syntax ns -> Annot ns -> m (Tm ns)

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
check : HasTc m => {md : TcMode} -> TcAt md m ns -> TcAt Check m ns
check {md = InferAt} f = \ctx, annot => (.tm) <$> (insertAt ctx annot.stage $ f ctx annot.stage)
check {md = Infer} f = \ctx, annot => (.tm) <$> (insert ctx $ f ctx)
check {md = Check} f = f

-- 0 Run : HasTc m => {md : TcMode} -> Tc m Check ns -> Type
-- Run {md = Check} c =

identsMatch : Ident -> Ident -> Bool
identsMatch (Implicit, n) (Implicit, m) = n == m
identsMatch (Explicit, _) (Explicit, _) = True
identsMatch _ _ = False

sizedObjType : (size : Val ns) -> ValTy ns
sizedObjType size = SimpPrimNormal (SimpApplied PrimUnsized
    [(SimpPrimNormal (SimpApplied PrimEmbedBYTES [size]))])

zeroBytes : Val ns
zeroBytes = SimpPrimNormal (SimpApplied PrimZeroBYTES [])

mtaType : ValTy ns
mtaType = SimpPrimNormal (SimpApplied PrimTYPE [])

sizedTypeOfTypes : Stage -> Annot ns
sizedTypeOfTypes Mta = MkAnnot mtaType Mta
sizedTypeOfTypes Obj = MkAnnot (sizedObjType zeroBytes) Obj

unify : HasTc m => Context ns -> Val ns -> Val ns -> m ()

-- Evaluate a closure with a extended environment
evalClosure : Context ns -> Body Value n ns -> Term Value (ns :< n')
evalClosure ctx (Closure env body) = eval (lift ctx.size env) body

sLam : Stage -> (n : Ident) -> Term Syntax (ns :< n) -> Term Syntax ns
sLam s n t = SynApps (SynBinding s Callable (Bound s (BindLam n) (Delayed t)) $$ [])

vPi : Stage -> (n : Ident) -> ValTy ns -> Body Value n ns -> Term Value ns
vPi s n ty body = RigidBinding s (Bound s (BindPi n ty) body)

-- lamInfer : HasTc m
--   => (n : Ident)
--   -> {md : TcMode}
--   -> (bindTy : Maybe (Tc md m ns))
--   -> (body : Tc md m (ns :< n))
--   -> Tc Infer m ns

insertLam : HasTc m => Context ns
  -> (piStage : Stage)
  -> (piIdent : Ident)
  -> (bindTy : ValTy ns)
  -> (body : Body Value piIdent ns)
  -> {md : TcMode} -> (subject : Tc md m)
  -> m (ExprAt piStage Syntax ns)
insertLam ctx piStage piIdent bindTy body subject = do
  let b = evalClosure ctx body
  s <- check subject (bind piIdent (MkAnnot bindTy piStage) ctx) (MkAnnot b piStage)
  pure $ MkExprAt (sLam piStage piIdent s) (vPi piStage piIdent bindTy body)

closeHere : Context ns -> Ty (ns :< n) -> Body Value n ns
closeHere ctx ty = Closure (id ctx.size) ty

ifForcePi : (HasTc m) => Context ns
  -> (mode : PiMode)
  -> (potentialPi : ValTy ns)
  -> (ifMatching : (piStage : Stage) -> (piIdent : Ident) -> (a : ValTy ns) -> (b : Body Value piIdent ns) -> m r)
  -> (ifMismatching : (piStage : Stage) -> (piIdent : Ident) -> (a : ValTy ns) -> (b : Body Value piIdent ns) -> m r)
  -> m r
ifForcePi ctx mode potentialPi ifMatching ifMismatching
  = resolve potentialPi >>= \case
    RigidBinding piStage (Bound piStage (BindPi piIdent a) b) =>
      if fst piIdent == mode
        then ifMatching piStage piIdent a b
        else ifMismatching piStage piIdent a b
    _ => do
      a <- freshMetaVal ctx
      let piIdent = (mode, "_")
      let piStage = Mta
      b <- closeHere ctx <$> freshMeta (bind piIdent (MkAnnot a piStage) ctx)
      unify ctx potentialPi (vPi piStage piIdent a b)
      ifMatching piStage piIdent a b

tcLam : HasTc m => (md : TcMode)
  -> (n : Ident)
  -> {md' : TcMode}
  -> (bindTy : Maybe (Tc md' m))
  -> (body : Tc md' m)
  -> Tc md m
tcLam @{tc} Check lamIdent bindTy body = \ctx, annot@(MkAnnot ty resultStage) => do
  ifForcePi ctx (fst lamIdent) ty
    (\piStage, piIdent, a, b => do
      annotTy : Annot ns <- case bindTy of
        Nothing => pure $ MkAnnot a piStage
        Just bindTy => do
          bindTy' <- evaluate ctx <$> check bindTy ctx (sizedTypeOfTypes piStage)
          unify ctx a bindTy'
          pure $ MkAnnot bindTy' piStage
      bodyExpr <- check body (bind lamIdent annotTy ?ctx) (MkAnnot (evalClosure ctx b) piStage)
      pure $ sLam piStage lamIdent bodyExpr
    )
    (\piStage, piIdent, a, b => case fst piIdent of
      Implicit => (.tm) <$> insertLam {md = Infer} ctx piStage piIdent a b (tcLam Infer lamIdent bindTy body)
      _ => ?error
    )
    -- RigidBinding piStage (Bound piStage (BindPi piIdent@(piMode, _) a) b) =>
    --   if identsMatch lamIdent piIdent then do
    --     annotTy : Annot ns <- case bindTy of
    --       Nothing => pure $ MkAnnot a piStage
    --       Just bindTy => do
    --         bindTy' <- evaluate ctx <$> check bindTy ctx (sizedTypeOfTypes piStage)
    --         unify ctx a bindTy'
    --         pure $ MkAnnot bindTy' piStage
    --     bodyExpr <- check body (bind lamIdent annotTy ctx) (MkAnnot (evalClosure ctx b) piStage)
    --     pure $ sLam piStage lamIdent bodyExpr
    --   else if piMode == Implicit then
    --     ?fjsdlkfjl
    --     -- pure $ lam piStage piIdent bodyExpr
    --   else ?fafafa
    -- _ => check {md = Infer} (tcLam Infer lamIdent bindTy body) ctx annot
tcLam Infer lamIdent bindTy body = ?fab
tcLam InferAt lamIdent bindTy body = ?fac

-- tcLam : HasTc m => (s : Stage) -> (n : Ident) -> Tc m md (ns :< n) -> Tc m Check ns
-- tcLam st n body = InCheck $ \ctx, ty => ?fa
