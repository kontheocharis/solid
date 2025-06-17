-- Typechecking combinators for the core language.
module Core.Typechecking

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Core.Base
import Core.Primitives
import Core.Syntax
import Core.Evaluation
import Core.Rules
import Core.Metavariables
import Core.Unification
import Core.Atoms

%default covering

-- Typechecking modes
public export
data TcMode : Type where
  -- Check against a type, produce an elaborated term
  Check : TcMode
  -- Infer to produce an elaborated term and type
  Infer : TcMode

-- Typechecking errors, context-aware
public export
data TcErrorAt : Ctx -> Type where
  -- An error arising from unification
  WhenUnifying : Atom ns -> Atom ns -> Unification ns -> TcErrorAt ns
  -- Mismatching pi modes
  WrongPiMode : PiMode -> AtomTy ns -> TcErrorAt ns
  -- Cannot infer stage
  CannotInferStage : TcErrorAt ns
  -- Cannot find a name
  UnknownName : Name -> TcErrorAt ns
  -- Too many applications
  TooManyApps : (less : Count ar) -> TcErrorAt ns
  -- Not enough applications
  TooFewApps : (more : Count ar) -> TcErrorAt ns


-- Context for typechecking
public export
record Context (ns : Ctx) where
  constructor MkContext
  -- All the identifiers in scope
  idents : Singleton ns
  -- The current context of types
  con : Con AtomTy ns
  -- The current context of sorts
  sorts : Con AtomTy ns
  -- The definitions in the context
  --
  -- This is an endomorphism of `con`; bindings are mapped to their level, and
  -- definitions are mapped to their value.
  defs : Sub ns Atom ns
  -- The stages of the definitions in the context
  stages : Con (const Stage) ns
  -- The size of the context, for quick access
  size : Size ns
  -- The bound variables in the context, in the form of a spine ready to be applied
  -- to a metavariable.
  binds : Exists (\ar => Spine ar AtomTy ns)
  
public export
emptyContext : Context [<]
emptyContext =
  MkContext (Val [<]) [<] [<] [<] [<] SZ (Evidence [] [])

-- A goal is a hole in a context.
public export
record Goal where
  constructor MkGoal
  {0 conNs : Ctx}

  -- The name of the goal hole, if given
  name : Maybe Name

  -- The actual hole term and its type
  hole : Expr conNs

  -- The context in which the goal exists
  ctx : Context conNs
  
%hint
ctxSize : Context ns -> Size ns
ctxSize = .size

-- Find a name in the context
lookup : Context ns -> Name -> Maybe (Idx ns)
lookup ctx n = findIdx ctx.idents n
  where
    findIdx : forall ns . Singleton ns -> Name -> Maybe (Idx ns)
    findIdx (Val [<]) n = Nothing
    findIdx (Val (ns :< (m, n'))) n = case n == n' of
      True => Just IZ
      False => do
        idx <- findIdx (Val ns) n
        pure $ IS idx

-- Packaging an error with its context
public export
record TcError where
  constructor MkTcError
  {0 conNs : Ctx}
  -- The context in which the error occurred
  con : Context conNs
  -- The location of the error in the source file
  loc : Loc
  -- The error itself
  err : TcErrorAt conNs
  
export
Show (TcErrorAt ns) where
  show (WhenUnifying x y z) = ?fafa_0
  show (WrongPiMode x y) = ?fafa_1
  show CannotInferStage = ?fafa_2
  show (UnknownName str) = ?fafa_3
  show (TooManyApps less) = ?fafa_4
  show (TooFewApps more) = ?fafa_5
  
export
Show TcError where
  show (MkTcError con loc err) = ?showTcError_0

-- Add a potentially self-referencing definition to the context.
addToContext : {s : Stage} -> (isBound : Bool) -> (n : Ident) -> AnnotAt s ns -> Atom (ns :< n) -> Context ns -> Context (ns :< n)
addToContext {s = stage} isBound n (MkAnnotAt ty sort) tm (MkContext (Val idents) con sorts defs stages size (Evidence ar bounds)) =
  MkContext
    (Val (idents :< n)) (con :< ty) (sorts :< sort) (defs `o` Drop Id :< tm) (stages :< stage) (SS size)
    (if isBound then (Evidence (ar ++ [n]) $ wkS bounds ++ [(Val _, tm)]) else (Evidence ar $ wkS bounds))

-- Add a definition to the context that lazily evaluates to its value.
define : {s : Stage} -> (n : Ident) -> ExprAt s ns -> Context ns -> Context (ns :< n)
define n rhs ctx =
  addToContext False n rhs.annot (promote $ Glued (LazyApps (ValDef (Level here) $$ []) (wk rhs.tm.val))) ctx

-- Add a binding with no value to the context.
bind : {s : Stage} -> (n : Ident) -> AnnotAt s ns -> Context ns -> Context (ns :< n)
bind n annot ctx = addToContext True n annot here ctx

-- Typechecking has access to metas
public export
interface (Monad m) => HasTc m where
  
  -- Explicit instance of metas so that the resolution doesn't die..
  0 metasM : SolvingMode -> Type -> Type
  enterMetas : {sm : SolvingMode} -> metasM sm t -> m t
  metas : HasMetas metasM

  -- Throw a typechecking error
  tcError : Context ns -> TcErrorAt ns -> m a

  -- Set the current typechecking location in the source file
  enterLoc : Loc -> m a -> m a

  -- Add a user goal
  addGoal : Goal -> m ()

  -- Get all the goals that have been seen
  getGoals : m (SnocList Goal)

-- This is the type over which we build the typechecking combinators.
--
-- `TcOp m md ns` is a typechecking operation in mode md.
--
-- It can be executed to produce an elaborated expression, depending on what `md` is.
public export
0 TcOp : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcOp Check m ms = {s : Stage} -> AnnotAt s ms -> m (Atom ms)
TcOp Infer m ms = (s : Maybe Stage) -> m (ExprAtMaybe s ms)

-- Typechecking in a specific context
public export
0 TcAt : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcAt md m ns = Context ns -> TcOp md m ns

-- Typechecking in any context
--
-- This is what is mostly used to work with, since a lot of the time we don't know which
-- context we will switch in ahead of time (due to things like inserted lambdas).
public export
0 Tc : (md : TcMode) -> (0 m : Type -> Type) -> Type
Tc md m = forall ns . TcAt md m ns

-- Typechecking at any mode and context.
export
0 TcAll : (m : Type -> Type) -> Type
TcAll m = {md : TcMode} -> Tc md m

export
runAt : (md : TcMode) -> TcAll m -> Tc md m
runAt md f = f {md = md}

-- Map a parametric monadic operation over Tc.
public export
intercept : HasTc m => (forall a . m a -> m a) -> {md : TcMode} -> Tc md m -> Tc md m
intercept f {md = Check} x = \ctx, as => f (x ctx as)
intercept f {md = Infer} x = \ctx, s => f (x ctx s)

-- Map a parametric monadic operation over TcAll.
public export
interceptAll : HasTc m => (forall a . m a -> m a) -> TcAll m -> TcAll m
interceptAll f x {md = Check} = \ctx, as => f (x {md = Check} ctx as)
interceptAll f x {md = Infer} = \ctx, s => f (x {md = Infer} ctx s)

public export
mightKnowStage : HasTc m => (s : Maybe Stage) -> TcAll m -> TcAll m
-- mightKnowStage Nothing f = f
-- mightKnowStage (Just s) f {md = Check} = 

-- Some useful shorthands

resolve : HasTc m => Size ns => Atom ns -> m (Atom ns)
resolve x = do
  t <- enterMetas $ resolveGlueAndMetas {sm = SolvingAllowed} @{metas} x.val
  pure $ promote t

promoteWithoutDefs : Size ns -> {d : Domain} -> Term d ns -> Atom ns
promoteWithoutDefs s {d = Syntax} tm = Choice tm (eval id tm)
promoteWithoutDefs s {d = Value} val = Choice (quote val) val

-- Create a fresh metavariable
freshMeta : HasTc m => Context ns -> Maybe Name -> AnnotAt s ns -> m (ExprAt s ns)
freshMeta ctx n annot = do -- @@Todo: use type
  m <- enterMetas $ newMeta {sm = SolvingAllowed} @{metas} n
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure $ meta m (snd ctx.binds) annot

-- Insert all lambdas implicit lambdas in a type-directed manner, without regard
-- for what the expression is.
insertAll : (HasTc m) => Context ns -> m (Expr ns) -> m (Expr ns)

-- Insert all lambdas implicit lambdas in a type-directed manner, unless the given expression is a
-- matching implicit lambda.
insert : (HasTc m) => Context ns -> m (Expr ns) -> m (Expr ns)

-- Stage-aware `insert`.
insertAt : (HasTc m) => Context ns -> {s : Stage} -> m (ExprAt s ns) -> m (ExprAt s ns)

-- Insert until a given name is reached.
insertUntil : (HasTc m) => Context ns -> Name -> m (Expr ns) -> m (Expr ns)

-- Ensure that the given `Maybe Stage` is `Just _`, eliminating with the
-- supplied method.
ensureKnownStage : HasTc m
  => (Context ns -> (s : Stage) -> m (ExprAt s ns))
  -> Context ns
  -> (ms : Maybe Stage)
  -> m (ExprAtMaybe ms ns)
ensureKnownStage f ctx (Just s) = f ctx s
ensureKnownStage f ctx Nothing = tcError ctx CannotInferStage


-- Try to adjust the stage of an expression.
tryAdjustStage : (HasTc m) => Context ns -> Expr ns -> (s : Stage) -> m (Maybe (ExprAt s ns))

-- Adjust the stage of an expression.
adjustStage : (HasTc m) => Context ns -> Expr ns -> (s : Stage) -> m (ExprAt s ns)

adjustStageIfNeeded : (HasTc m) => Context ns -> Expr ns -> (s : Maybe Stage) -> m (ExprAtMaybe s ns)
adjustStageIfNeeded ctx expr Nothing = pure expr
adjustStageIfNeeded ctx expr (Just s) = adjustStage ctx expr s

-- Coerce an expression to a given type.
coerce : (HasTc m) => Expr ns -> Annot ns -> m (Tm ns)

-- Unify two values in the given context.
--
-- Succeeds if the unification says `AreSame`.
unify : HasTc m => Context ns -> Atom ns -> Atom ns -> m ()
unify ctx a b = do
  val : Unification _ <- enterMetas (unify {sm = SolvingAllowed} @{unifyValues @{metas}} a.val b.val)
  case val of
    AreSame => pure ()
    failure => tcError ctx $ WhenUnifying a b failure

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
public export
switch : HasTc m => Tc Infer m -> TcAll m
switch f {md = Infer} = f
switch f {md = Check} = \ctx, annot => do
  result <- insertAt ctx $ f ctx (Just (packStage annot).stage)
  unify ctx annot.ty result.annot.ty
  pure result.tm
  
-- Create a `SortData` instance for the given stage and sort kind, by instantiating metas
-- for the unknown information (byte sizes).
freshSortData : HasTc m => Context ns -> (s : Stage) -> (k : SortKind s) -> m (SortData s k ns)
freshSortData ctx Mta k = pure $ MtaSort 
freshSortData ctx Obj Dyn = do
  b <- freshMeta ctx Nothing psBytesAnnot
  pure $ ObjSort Dyn b.tm
freshSortData ctx Obj Sized = do
  b <- freshMeta ctx Nothing staBytesAnnot
  pure $ ObjSort Sized b.tm
  
-- Create a fresh annotation for the given stage and sort kind.
freshMetaAnnot : HasTc m => Context ns -> (s : Stage) -> SortKind s -> m (AnnotAt s ns)
freshMetaAnnot ctx s k = do
  tySort <- freshSortData ctx s k <&> .asAnnot
  ty <- freshMeta ctx Nothing tySort
  pure $ MkAnnotAt ty.tm tySort.ty
  
-- Fit the given annotation to the given kind.
fitAnnot : HasTc m => Context ns -> (s : Stage) -> (k : SortKind s) -> (annotTy ns, AtomTy ns) -> m (AnnotFor s k annotTy ns)
fitAnnot ctx s k (vty, univ) = do
  d <- freshSortData ctx s k
  unify ctx univ d.asAnnot.ty
  pure $ MkAnnotFor d vty

-- Insert (some kind of an implicit) lambda from the given information.
--
-- This adds the binder to the subject and 'recurses', yielding a lambda with the
-- given Pi type.
insertLam : HasTc m => Context ns
  -> (piStage : Stage)
  -> (piIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (AtomBody piIdent) ns)
  -> (subject : Tc Check m)
  -> m (ExprAt piStage ns)
insertLam ctx piStage piIdent bindAnnot bodyAnnot subject = do
  s <- subject (bind piIdent bindAnnot.asAnnot ctx)
        (bodyAnnot.inner.open `asTypeIn` (wkS $ typeOfTypeAnnot piStage))
  pure $ lam piStage piIdent piIdent bindAnnot bodyAnnot (close ctx.defs s)
  
-- Infer the given object as a type, also inferring its stage in the process.
inferAnnot : HasTc m => Context ns -> (k : forall s . SortKind s) -> Tc Infer m -> m (s ** AnnotFor s k Atom ns)
inferAnnot ctx kind ty = do
  MkExpr t (MkAnnot univ _ stage) <- ty ctx Nothing
  res <- fitAnnot ctx stage kind {annotTy = AtomTy} (t, univ)
  pure (stage ** res)

-- Check a spine against a telescope.
--
-- Returns the checked spine and the remaining terms in the input.
checkSpine : HasTc m
  => Context ns
  -> List (Ident, TcAll m)
  -> Tel ar Annot ns
  -> m (Spine ar Atom ns)
checkSpine ctx tms [] = tcError ctx (TooManyApps (map fst tms).count)
checkSpine ctx [] annots = tcError ctx (TooFewApps annots.count)
checkSpine ctx ((_, tm) :: tms) ((Val _, annot) :: annots) = do -- @@Todo: spine name
  tm' <- tm {md = Check} ctx (forgetStage annot)
  tms' <- checkSpine ctx tms (sub (ctx.defs :< tm') annots)
  pure ((Val _, tm') :: tms')
  
-- Main combinators:

-- Introduce a metavariable
public export
tcMeta : HasTc m => {default Nothing name : Maybe Name} -> TcAll m
tcMeta {md = Check} {name = name} = \ctx, annot => do
  mta <- freshMeta ctx name annot
  whenJust name $ \n => addGoal (MkGoal (Just n) (packStage mta) ctx)
  pure mta.tm
tcMeta {md = Infer} {name = name} = ensureKnownStage $ \ctx, stage => do
  annot <- freshMetaAnnot ctx stage Dyn -- remember, sized < dyn
  mta <- freshMeta ctx name annot
  whenJust name $ \n => addGoal (MkGoal (Just n) (packStage mta) ctx)
  pure mta

-- Check a function type.
public export
tcPi : HasTc m
  => Ident
  -> TcAll m
  -> TcAll m
  -> TcAll m
tcPi x a b = switch $ ensureKnownStage $ \ctx, stage => case stage of
  -- @@Reconsider: Kovacs infers the stage from the domain if it is not given..
  -- This is more annoying here because of byte metas, but also I am not
  -- convinced that it is the right thing to do. It might lead to some weird elab results.
  Mta => do
    let aSort = mtaTypeAnnot
    a' <- a {md = Check} ctx aSort
    b' <- b {md = Check} (bind x (a' `asTypeIn` aSort) ctx) (wkS mtaTypeAnnot)
    pure $ pi Mta x (MkAnnotFor MtaSort a') (MkAnnotFor MtaSort (close ctx.defs b'))
  Obj => do
    ba <- freshMeta ctx Nothing staBytesAnnot
    bb <- freshMeta ctx Nothing staBytesAnnot
    let aSort = sizedObjTypeAnnot ba.tm
    a' <- a {md = Check} ctx aSort
    b' <- b {md = Check} (bind x (a' `asTypeIn` aSort) ctx) (wkS $ sizedObjTypeAnnot bb.tm)
    pure $ pi Obj x (MkAnnotFor (ObjSort Sized ba.tm) a') (MkAnnotFor (ObjSort Sized bb.tm) (close ctx.defs b'))

-- Check a lambda abstraction.
public export
tcLam : HasTc m
  => (n : Ident)
  -> (bindTy : Maybe (TcAll m))
  -> (body : TcAll m)
  -> TcAll m
tcLam lamIdent bindTy body {md = Check} = \ctx, annot@(MkAnnotAt ty sort) => do
  let stage = (packStage annot).stage
  -- We must switch that the type we have is a pi
  resolve ty >>= \ty' => ifForcePi stage lamIdent ty'
    (\resolvedPi, piIdent, a, b => do
      -- Great, it is a pi. Now first reconcile this with the annotation type
      -- of the lambda.
      whenJust bindTy $ \bindTy' => do
        MkExprAt bindPi _ <- tcPi lamIdent bindTy' tcMeta {md = Infer} ctx (Just stage)
        unify ctx resolvedPi bindPi

      -- Then switch the body with the computed annotation type.
      body' <- body {md = Check}
        (bind lamIdent (a.asAnnot) ctx)
        (b.open.asAnnot)
      
      -- Produce the appropriate lambda based on the stage.
      pure $ (lam stage piIdent lamIdent a b (close ctx.defs body')).tm
    )
    (\piStage, resolvedPi, piIdent, a, b => case fst piIdent of
      -- It wasn't the right kind of pi; if it was implicit, insert a lambda
      Implicit => do
        MkExprAt tm _ <- insertLam ctx piStage piIdent a b (tcLam {md = Check} lamIdent bindTy body)
        pure tm
      -- Otherwise, we have the wrong kind of pi.
      _ => tcError ctx (WrongPiMode (fst piIdent) resolvedPi)
    )
    (\other => do
      -- Otherwise try unify with a constructed pi
      createdPi <- tcPi lamIdent tcMeta tcMeta {md = Infer} ctx (Just stage)
      unify ctx other createdPi.tm
      tcLam {md = Check} lamIdent bindTy body ctx {s = stage} createdPi.toAnnot
    )
tcLam lamIdent bindTy body {md = Infer} = ensureKnownStage $ \ctx, stage => do
  -- @@Reconsider: Same remark as for pis.
  -- We have a stage, but no type, so just instantiate a meta..
  annot <- freshMetaAnnot ctx stage Sized
  res <- tcLam {md = Check} lamIdent bindTy body ctx annot
  pure $ MkExprAt res annot

-- Check a variable, by looking up in the context
public export
tcVar : HasTc m => Name -> TcAll m
tcVar n = switch $ \ctx, stage' => case lookup ctx n of
    Nothing => tcError ctx $ UnknownName n
    Just idx => do
      let tm = var idx (MkAnnotAt {s = ctx.stages.indexS idx} (ctx.con.indexS idx) (ctx.sorts.indexS idx))
      adjustStageIfNeeded ctx (packStage tm) stage'

-- Infer or switch a user-supplied hole
--
-- We should at least know the stage of the hole. User holes are added to the
-- list of goals, which can be displayed after typechecking.
public export
tcHole : HasTc m => Maybe Name -> TcAll m
tcHole n = tcMeta {name = n}

-- Check an application
public export
tcApp : HasTc m
  => (subject : TcAll m)
  -> List (Ident, TcAll m)
  -> TcAll m

-- Check a primitive
public export
tcPrim : HasTc m
  => Count ar
  => {r : PrimitiveReducibility}
  -> {k : PrimitiveClass}
  -> Primitive k r ar
  -> List (Ident, TcAll m)
  -> TcAll m
tcPrim p args = switch $ \ctx, stage => do
  let (pParams, _) = primAnnot p
  sp <- checkSpine ctx args pParams
  adjustStageIfNeeded ctx (prim p sp) stage
  
-- Check the unit type or term.
public export
tcUnit : HasTc m => TcAll m
tcUnit {md = Check} = \ctx, annot => do
  ?fa
tcUnit {md = Infer} = \ctx, annot => do
  ?fb
  -- let stage = (packStage annot).stage
  -- adjustStageIfNeeded ctx (unitForStage stage) stage
  
-- Check a sigma type
public export
tcSigma : HasTc m
  => Ident
  -> TcAll m
  -> TcAll m
  -> TcAll m

-- Check an iterated pair
public export
tcPairs : HasTc m
  => List (Ident, TcAll m)
  -> TcAll m

-- Check a named pair projection
public export
tcProj : HasTc m
  => (subject : TcAll m)
  -> (member : Name)
  -> TcAll m
  
-- Check a let statement.
public export
tcLet : HasTc m
  => Name
  -> Maybe Stage
  -> (Maybe (TcAll m))
  -> TcAll m
  -> TcAll m
  -> TcAll m
  
-- Check a let-rec statement.
public export
tcLetRec : HasTc m
  => Name
  -> Maybe Stage
  -> TcAll m
  -> TcAll m
  -> TcAll m
  -> TcAll m