-- Typechecking combinators for the core language.
module Core.Typechecking

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Data.Maybe
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Metavariables
import Core.Unification
import Core.Atoms
import Core.Combinators
import Core.Primitives.Typing

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
  -- Tried to apply something that isn't a pi type
  NotAPi : (subj : AtomTy ns) -> (extra : Count ar) -> TcErrorAt ns


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
(ns : Ctx) => ShowSyntax => Show (Unification ns) where
  show AreSame = "terms are the same"
  show AreDifferent = "terms are different"
  show DontKnow = "terms are not the same"
  show (Error x) = "unification error: \{show x}"

export
(ns : Ctx) => ShowSyntax => Show (TcErrorAt ns) where
  show (WhenUnifying x y z) = "When unifying \{show x} with \{show y}: \{show z}"
  show (WrongPiMode mode ty) = "Wrong pi mode \{show mode} for type \{show ty}"
  show CannotInferStage = "Cannot infer stage"
  show (UnknownName name) = "Unknown name: \{show name}"
  show (TooManyApps count) = "Too many applications (expected \{show count} fewer)"
  show (TooFewApps count) = "Too few applications (expected \{show count} more)"
  show (NotAPi subj extra) = "The type of the subject is \{
      show subj
    } but tried to apply it to \{
      show extra
    } argument(s), which is too many"
  
export
ShowSyntax => Show TcError where
  show (MkTcError con loc err) = let Val _ = con.idents in
      "Typechecking error at \{show loc}:\n\{show err}"

-- Add a potentially self-referencing definition to the context.
addToContext : {s : Stage} -> (isBound : Bool) -> (n : Ident) -> AnnotAt s ns -> Atom (ns :< n) -> Context ns -> Context (ns :< n)
addToContext {s = stage}
  isBound n
  (MkAnnotAt ty sort)
  tm
  (MkContext (Val idents)
  con sorts defs stages size
  (Evidence ar bounds)) =
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
-- @@TODO: refactor to use lenses
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

  -- The signature of a declared primitive
  definedPrimAnnot : Primitive k r PrimDeclared ar -> m (Op ar [<])
  setDefinedPrimAnnot : Primitive k r PrimDeclared ar -> Op ar [<] -> m ()
  
-- What inputs a TC operation takes, depending on mode
public export
data TcInput : TcMode -> Ctx -> Type where
  CheckInput : (s : Stage) -> AnnotAt s ms -> TcInput Check ms
  InferInput : (s : Maybe Stage) -> TcInput Infer ms
  
export
WeakSized (TcInput md) where
  weakS e (CheckInput s a) = CheckInput s (weakS e a)
  weakS e (InferInput s) = InferInput s
  
public export
(.stage) : TcInput md ns -> Maybe Stage
(.stage) (CheckInput s _) = Just s
(.stage) (InferInput s) = s
  
public export
0 weakPreservesStage : Size ns => Size ms
  => {e : Wk ns ms}
  -> {i : TcInput md ms}
  -> (weakS e i).stage = i.stage
weakPreservesStage {i = CheckInput s a} = Refl
weakPreservesStage {i = InferInput s} = Refl
  
-- Outputs are expressions corresponding to the inputs
public export
0 TcOutput : (md : TcMode) -> (ms : Ctx) -> TcInput md ms -> Type
TcOutput md ms i = ExprAtMaybe i.stage ms
  
-- This is the type over which we build the typechecking combinators.
--
-- `TcOp m md ns` is a typechecking operation in mode md.
--
-- It can be executed to produce an elaborated expression, depending on what `md` is.
public export
0 TcOp : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcOp md m ms = (i : TcInput md ms) -> m (TcOutput md ms i)

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
public export
0 TcAll : (m : Type -> Type) -> Type
TcAll m = (md : TcMode) -> Tc md m

public export
runAt : HasTc m => (md : TcMode) -> TcAll m -> Tc md m
runAt md f = f md

-- Map a parametric monadic operation over Tc.
public export
intercept : HasTc m => (forall a . m a -> m a) -> {md : TcMode} -> Tc md m -> Tc md m
intercept f {md = Check} x = \ctx, as => f (x ctx as)
intercept f {md = Infer} x = \ctx, s => f (x ctx s)

-- Map a parametric monadic operation over TcAll.
public export
interceptAll : HasTc m => (forall a . m a -> m a) -> TcAll m -> TcAll m
interceptAll f x Check = \ctx, as => f (x Check ctx as)
interceptAll f x Infer = \ctx, s => f (x Infer ctx s)

-- Some useful shorthands

-- This should probably never be used.
-- promoteWithoutDefs : Size ns -> {d : Domain} -> Term d ns -> Atom ns
-- promoteWithoutDefs s {d = Syntax} tm = Choice tm (eval id tm)
-- promoteWithoutDefs s {d = Value} val = Choice (quote val) val

solving : HasTc m => (forall m' . HasMetas m' => m' SolvingAllowed t) -> m t
solving @{tc} f = enterMetas (f {m' = metasM @{tc}} @{metas @{tc}})

reading : HasTc m => (forall m' . HasMetas m' => m' SolvingNotAllowed t) -> m t
reading @{tc} f = enterMetas (f {m' = metasM @{tc}} @{metas @{tc}})

-- Create a fresh metavariable
freshMeta : HasTc m => Context ns -> Maybe Name -> AnnotAt s ns -> m (ExprAt s ns)
freshMeta ctx n annot = do -- @@Todo: use type
  m <- solving $ newMeta n
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure $ meta m (snd ctx.binds) annot

-- Unify two values in the given context.
--
-- Succeeds if the unification says `AreSame`.
public export
unify : HasTc m => Context ns -> Atom ns -> Atom ns -> m ()
unify @{tc} ctx a b = do
  val : Unification _ <- enterMetas (unify {sm = SolvingAllowed} @{metas} @{unifyValues} a.val b.val)
  case val of
    AreSame => pure ()
    failure => tcError ctx $ WhenUnifying a b failure

public export
areEqual : HasTc m => Context ns -> Atom ns -> Atom ns -> m (Unification ns)
areEqual @{tc} ctx a b = do
  enterMetas (unify {sm = SolvingNotAllowed} @{metas} @{unifyValues} a.val b.val)
  
-- Create a `SortData` instance for the given stage and sort kind, by instantiating metas
-- for the unknown information (byte sizes).
freshSortData : HasTc m => Context ns -> (s : Stage) -> (k : SortKind s) -> m (SortData s k ns)
freshSortData ctx Mta k = pure $ MtaSort 
freshSortData ctx Obj Dyn = do
  b <- freshMeta ctx Nothing layoutA.f
  pure $ ObjSort Dyn b.tm
freshSortData ctx Obj Sized = do
  b <- freshMeta ctx Nothing layoutDynA.f
  pure $ ObjSort Sized b.tm
  
-- Create a fresh annotation for the given stage and sort kind.
freshMetaAnnot : HasTc m => Context ns -> (s : Stage) -> SortKind s -> m (AnnotAt s ns)
freshMetaAnnot ctx s k = do
  tySort <- freshSortData ctx s k <&> .a
  ty <- freshMeta ctx Nothing tySort
  pure $ MkAnnotAt ty.tm tySort.ty

-- Fit the given annotation to the given kind.
fitAnnot : HasTc m
  => Context ns
  -> (s : Stage)
  -> (k : SortKind s)
  -> AnnotShape annotTy AtomTy ns
  -> m (AnnotFor s k annotTy ns)
fitAnnot ctx s k (MkAnnotShape vty univ) = do
  d <- freshSortData ctx s k
  unify ctx univ d.a.ty
  pure $ MkAnnotFor d vty

-- Ensure that the given `Maybe Stage` is `Just _`, eliminating with the
-- supplied method.
ensureKnownStage : HasTc m
  => (Context ns -> (s : Stage) -> m (ExprAt s ns))
  -> Context ns
  -> (i : TcInput Infer ns)
  -> m (ExprAtMaybe i.stage ns)
ensureKnownStage f ctx (InferInput (Just s)) = f ctx s
ensureKnownStage f ctx (InferInput Nothing) = tcError ctx CannotInferStage

-- Coerce an expression to a given type.
coerce : (HasTc m) => Expr ns -> Annot ns -> m (Tm ns)

-- Adjust the stage of an expression.
adjustStage : (HasTc m) => Context ns -> Expr ns -> (s : Stage) -> m (ExprAt s ns)

-- Adjust the stage of an expression if needed.
adjustStage' : (HasTc m) => Context ns -> Expr ns -> (s : Stage) -> m (Maybe (ExprAt s ns))
adjustStage' ctx e@(MkExpr tm (MkAnnot ty sort Obj)) Obj = pure Nothing
adjustStage' ctx e@(MkExpr tm (MkAnnot ty sort Mta)) Mta = pure Nothing
adjustStage' ctx e@(MkExpr tm ann@(MkAnnot ty sort s@Obj)) s'@Mta = do
  ann' <- fitAnnot ctx s (loosestSortKind s) ann.f.shape
  let e' = quot @{ctx.size} (mapAnnot (\_ => ann') e)
  pure $ Just (mapAnnot (\a => a.asAnnot) e')
adjustStage' ctx (MkExpr tm ann@(MkAnnot ty sort Mta)) s@Obj = ?kdo

adjustStageIfNeeded : (HasTc m) => Context ns -> Expr ns -> (s : Maybe Stage) -> m (ExprAtMaybe s ns)
adjustStageIfNeeded ctx expr Nothing = pure expr
adjustStageIfNeeded ctx expr (Just s) = adjustStage ctx expr s

-- Insert all implicit applications in a type-directed manner, without regard
-- for what the expression is.
insertAll : HasTc m => Context ns -> {s : Stage} -> m (ExprAt s ns) -> m (ExprAt s ns)
insertAll ctx mExpr = mExpr >>= insertAll' ctx
  where
    insertAll' : forall ns, m . HasTc m => Context ns -> {s : Stage} -> ExprAt s ns -> m (ExprAt s ns)
    insertAll' ctx expr = do
      let (MkExpr tm (MkAnnotAt ty sort)) = expr
      reading (forcePi ty) >>= \case
        MatchingPi stage (MkPiData resolvedPi (Implicit, piName) a b) => do
          subject <- freshMeta ctx Nothing a.asAnnot
          let res = apps expr.p
                [(Val (Implicit, piName), subject.p)]
                (apply b subject.tm).asAnnot
          adjustStage ctx res.p _ >>= insertAll' ctx
        _ => pure $ MkExpr tm (MkAnnotAt ty sort)

-- Insert all implicit applications in a type-directed manner, unless the given expression is a
-- matching implicit lambda.
insert : (HasTc m) => Context ns -> {s : Stage} -> m (ExprAt s ns) -> m (ExprAt s ns)
insert ctx mExpr = do
  expr@(MkExpr tm (MkAnnotAt ty sort)) <- mExpr
  reading (forceLam tm) >>= \case
    MatchingLam Mta (BindMtaLam (Implicit, name)) body => pure expr
    MatchingLam Obj (BindObjLam (Implicit, name) domBytes codBytes) body => pure expr
    _ => insertAll ctx (pure expr)

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
public export
switch : HasTc m => Tc Infer m -> TcAll m
switch f Infer = f
switch f Check = \ctx, (CheckInput stage annot) => do
  result <- insert ctx $ f ctx (InferInput (Just stage))
  unify ctx annot.ty result.annot.ty
  pure result

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
  s <- subject
    (bind piIdent bindAnnot.asAnnot ctx)
    (CheckInput _ (objZOrMta piStage (bodyAnnot.inner.open)).a.f)
  pure $ lam piStage piIdent piIdent bindAnnot bodyAnnot (close ctx.defs s.tm)
  
-- Infer the given object as a type, also inferring its stage in the process.
inferAnnot : HasTc m
  => Context ns
  -> (k : forall s . SortKind s)
  -> Tc Infer m
  -> m (s ** AnnotFor s k Atom ns)
inferAnnot ctx kind ty = do
  MkExpr t (MkAnnot univ _ stage) <- ty ctx (InferInput Nothing)
  res <- fitAnnot ctx stage kind (MkAnnotShape t univ)
  pure (stage ** res)

-- Check a spine against a telescope.
--
-- Returns the checked spine and the remaining terms in the input.
tcSpine : HasTc m
  => Context ns
  -> List (Ident, TcAll m)
  -> Tel ar Annot ns
  -> m (Spine ar Expr ns)
tcSpine ctx tms [] = tcError ctx (TooManyApps (map fst tms).count)
tcSpine ctx [] annots = tcError ctx (TooFewApps annots.count)
tcSpine ctx ((_, tm) :: tms) ((Val _, annot) :: annots) = do -- @@Todo: spine name
  tm' <- tm Check ctx (CheckInput _ annot.f)
  tms' <- tcSpine ctx tms (sub (ctx.defs :< tm'.tm) annots)
  pure ((Val _, tm'.p) :: tms')
  
-- Main combinators:

-- Introduce a metavariable
public export
tcMeta : HasTc m => {default Nothing name : Maybe Name} -> TcAll m
tcMeta {name = name} Check = \ctx, (CheckInput _ annot) => do
  mta <- freshMeta ctx name annot
  whenJust name $ \n => addGoal (MkGoal (Just n) mta.p ctx)
  pure mta
tcMeta {name = name} Infer = ensureKnownStage $ \ctx, stage => do
  annot <- freshMetaAnnot ctx stage Dyn -- remember, sized < dyn
  mta <- freshMeta ctx name annot
  whenJust name $ \n => addGoal (MkGoal (Just n) mta.p ctx)
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
    a' <- a Check ctx (CheckInput _ mtaA.f)
    b' <- b Check (bind x (mta a'.tm).f.a ctx) (CheckInput _ mtaA.f)
    pure $ pi Mta x (MkAnnotFor MtaSort a'.tm) (MkAnnotFor MtaSort (close ctx.defs b'.tm))
  Obj => do
    ba <- freshMeta ctx Nothing layoutA.f
    bb <- freshMeta ctx Nothing layoutA.f
    a' <- a Check ctx (CheckInput _ (objA ba.tm).f)
    b' <- b Check (bind x (obj ba.tm a'.tm).a.f ctx) (CheckInput _ (wkS $ objA bb.tm).f)
    pure $ pi Obj x
      (MkAnnotFor (ObjSort Sized ba.tm) a'.tm)
      (MkAnnotFor (ObjSort Sized bb.tm) (close ctx.defs b'.tm))

-- Check a lambda abstraction.
public export
tcLam : HasTc m
  => (n : Ident)
  -> (bindTy : Maybe (TcAll m))
  -> (body : TcAll m)
  -> TcAll m
tcLam lamIdent bindTy body Check = \ctx, (CheckInput stage annot@(MkAnnotAt ty sort)) => do
  reading (forcePiAt stage lamIdent ty) >>= \case
    MatchingPiAt (MkPiData resolvedPi piIdent a b) => do
      -- Pi matches
      whenJust bindTy $ \bindTy' => do
        MkExpr bindPi _ <- tcPi lamIdent bindTy' tcMeta Infer ctx (InferInput (Just stage))
        unify ctx resolvedPi bindPi
      body' <- body Check
        (bind lamIdent (a.asAnnot) ctx)
        (CheckInput _ (b.open.asAnnot))
      pure $ lam stage piIdent lamIdent a b (close ctx.defs body'.tm)
    MismatchingPiAt piStage (MkPiData resolvedPi piIdent a b) => case fst piIdent of
      -- Wasn't the right kind of pi; if it was implicit, insert a lambda
      Implicit => do
        tm' <- insertLam ctx piStage piIdent a b (tcLam lamIdent bindTy body Check)
        adjustStage ctx tm'.p stage
      -- Otherwise, we have the wrong kind of pi.
      _ => tcError ctx (WrongPiMode (fst piIdent) resolvedPi)
    OtherwiseNotPiAt other => do
      -- Otherwise try unify with a constructed pi
      createdPi <- tcPi lamIdent tcMeta tcMeta Infer ctx (InferInput (Just stage))
      unify ctx other createdPi.tm
      tcLam lamIdent bindTy body Check ctx (CheckInput stage createdPi.a)
tcLam lamIdent bindTy body Infer = ensureKnownStage $ \ctx, stage => do
  -- @@Reconsider: Same remark as for pis.
  -- We have a stage, but no type, so just instantiate a meta..
  annot <- freshMetaAnnot ctx stage Sized
  tcLam lamIdent bindTy body Check ctx (CheckInput _ annot)

-- Check a variable, by looking up in the context
public export
tcVar : HasTc m => Name -> TcAll m
tcVar n = switch $ \ctx, (InferInput stage') => case lookup ctx n of
    Nothing => tcError ctx $ UnknownName n
    Just idx => do
      let tm = var idx (MkAnnotAt {s = ctx.stages.indexS idx}
            (ctx.con.indexS idx)
            (ctx.sorts.indexS idx))
      adjustStageIfNeeded ctx tm.p stage'

-- Infer or switch a user-supplied hole
--
-- We should at least know the stage of the hole. User holes are added to the
-- list of goals, which can be displayed after typechecking.
public export
tcHole : HasTc m => Maybe Name -> TcAll m
tcHole n = tcMeta {name = n}

-- Check an application
public export
tcApps : HasTc m
  => TcAll m
  -> List (Ident, TcAll m)
  -> TcAll m
tcApps subject args = switch $ \ctx, (InferInput reqStage) => do
  subject'@(MkExpr _ fnAnnot) <- (.mp) <$> subject Infer ctx (InferInput reqStage)
  reading (gatherPis fnAnnot (map fst args)) >>= \case
    Gathered params ret => do
      args' <- tcSpine ctx args params
      let result = apps subject' args'
            -- @@Refactor: why does it have to be like this :((
            (sub {tm = AnnotAt _} @{%search} @{ctx.size}
              @{ctx.size + args'.count}
              (ctx.defs ::< (map (.tm) args')) ret.f)
      adjustStageIfNeeded ctx result.p reqStage
    TooMany extra under p => tcError ctx $ NotAPi fnAnnot.ty extra

-- Check a primitive
public export
tcPrim : HasTc m
  => {ar : _}
  -> {r : PrimitiveReducibility}
  -> {k : PrimitiveClass}
  -> {l : PrimitiveLevel}
  -> Primitive k r l ar
  -> DispList ar (TcAll m)
  -> TcAll m
tcPrim p args = switch $ \ctx, (InferInput stage) => do
  (pParams, pRet) : Op _ _ <- case l of
    PrimNative => pure $ primAnnot p
    PrimDeclared => do
     (pParams, pRet) <- definedPrimAnnot p
     pure (
        evalS {over = Atom} [<] pParams,
        evalS {over = Atom} {sz = ctx.size + ar.count} {sz' = SZ + ar.count} (liftSMany [<]) pRet
      )
  sp <- tcSpine ctx (dispToList args) pParams
  adjustStageIfNeeded ctx (prim p (map (.tm) sp) pRet) stage
  
inferStageIfNone : HasTc m => Maybe Stage -> (Stage -> TcAll m) -> TcAll m
inferStageIfNone (Just s) m = m s
inferStageIfNone Nothing m = \md, ctx, inp => case inp of
  CheckInput s _ => m s md ctx inp
  InferInput (Just s) => m s md ctx inp
  InferInput Nothing => tcError ctx CannotInferStage
  
-- Check a let statement.
public export
tcLet : HasTc m
  => (name : Name)
  -> (stage : Maybe Stage)
  -> (ty : (Maybe (TcAll m)))
  -> (tm : TcAll m)
  -> (rest : TcAll m)
  -> TcAll m
tcLet name stage ty tm rest = inferStageIfNone stage $ \stage, md, ctx, inp => do
  let Val ns = ctx.idents
  tm' : ExprAt stage ns <- case ty of
    Just ty => do
      ty' <- ty Check ctx (CheckInput stage (objZOrMtaA stage))
      tm Check ctx (CheckInput stage ty'.a)
    Nothing => tm Infer ctx (InferInput (Just stage))
  rest' <- rest md (define (Explicit, name) tm' ctx) (wkS inp)
  let result = sub @{evalExprAtMaybe} {sns = ctx.size} {sms = SS ctx.size} (ctx.defs :< tm'.tm) rest'
  pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result
  
-- Check a declaration statement.
public export
tcDecl : HasTc m
  => (name : Name)
  -> (stage : Maybe Stage)
  -> (ty : TcAll m)
  -> (isPrimitive : Bool)
  -> (rest : TcAll m)
  -> TcAll m
tcDecl name stage ty tm rest = inferStageIfNone stage $ \stage, md, ctx, inp => ?ajko
  -- let Val ns = ctx.idents
  -- tm' : ExprAt stage ns <- case ty of
  --   Just ty => do
  --     ty' <- ty Check ctx (CheckInput stage (objZOrMtaA stage))
  --     tm Check ctx (CheckInput stage ty'.a)
  --   Nothing => tm Infer ctx (InferInput (Just stage))
  -- rest' <- rest md (define (Explicit, name) tm' ctx) (wkS inp)
  -- let result = sub @{evalExprAtMaybe} {sns = ctx.size} {sms = SS ctx.size} (ctx.defs :< tm'.tm) rest'
  -- pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result
  
-- Check a let-rec statement.
public export
tcLetRec : HasTc m
  => (name : Name)
  -> (stage : Maybe Stage)
  -> (ty : (TcAll m))
  -> (tm : TcAll m)
  -> (rest : TcAll m)
  -> TcAll m
tcLetRec name stage ty tm rest = inferStageIfNone stage $ \stage, md, ctx, inp => do
  let Val ns = ctx.idents
  ty' <- ty Check ctx (CheckInput stage (objZOrMtaA stage))
  tm' <- tm Check (bind (Explicit, name) ty'.a ctx) (CheckInput stage (wkS ty'.a))
  ?ajaja
  -- rest' <- rest md (define (Explicit, name) tm' ?ctx) (wkS inp)
  -- let result = sub @{evalExprAtMaybe} {sns = ctx.size} {sms = SS ctx.size} (ctx.defs :< tm'.tm) rest'
  -- pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result