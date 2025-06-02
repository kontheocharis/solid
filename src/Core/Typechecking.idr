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
data TcMode : Type where
  -- Check against a type, produce an elaborated term
  Check : TcMode
  -- Infer to produce an elaborated term and type
  Infer : TcMode

-- Typechecking errors, context-aware
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
  TooManyApps : Expr ns -> Spine ar Atom ns -> TcErrorAt ns

-- A goal is a hole in a context.
record Goal where
  constructor MkGoal

  -- The context in which the goal exists
  {0 conNs : Ctx}
  ctx : Con ValTy conNs

  -- The actual hole term and its type
  hole : Expr conNs

  -- The name of the goal hole, if given
  name : Maybe Name

-- Context for typechecking
record Context (ns : Ctx) where
  constructor MkContext
  -- All the identifiers in scope
  idents : Singleton ns
  -- The current context of types
  con : Con ValTy ns
  -- The current context of sorts
  sorts : Con ValTy ns
  -- The definitions in the context
  --
  -- This is an endomorphism of `con`; bindings are mapped to their level, and
  -- definitions are mapped to their value.
  defs : Sub ns Val ns
  -- The stages of the definitions in the context
  stages : Con (const Stage) ns
  -- The size of the context, for quick access
  size : Size ns
  -- The bound variables in the context, in the form of a spine ready to be applied
  -- to a metavariable.
  binds : Exists (\ar => Spine ar ValTy ns)
  
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
record TcError where
  constructor MkTcError
  {0 conNs : Ctx}
  -- The context in which the error occurred
  con : Context conNs
  -- The location of the error in the source file
  loc : Loc
  -- The error itself
  err : TcErrorAt conNs

-- Add a potentially self-referencing definition to the context.
addToContext : (isBound : Bool) -> (n : Ident) -> Annot ns -> Val (ns :< n) -> Context ns -> Context (ns :< n)
addToContext isBound n (MkAnnot ty sort stage) tm (MkContext (Val idents) con sorts defs stages size (Evidence ar bounds)) =
  MkContext
    (Val (idents :< n)) (con :< ty.val) (sorts :< sort.val) (defs . Drop Id :< tm) (stages :< stage) (SS size)
    (if isBound then (Evidence (ar ++ [n]) $ wk bounds ++ [tm]) else (Evidence ar $ wk bounds))

-- Add a definition to the context that lazily evaluates to its value.
define : (n : Ident) -> Expr ns -> Context ns -> Context (ns :< n)
define n rhs ctx =
  addToContext False n rhs.annot (Glued (LazyApps (ValDef (Level (lastLvl ctx.size)) $$ []) (wk rhs.tm.val))) ctx

-- Add a binding with no value to the context.
bind : (n : Ident) -> Annot ns -> Context ns -> Context (ns :< n)
bind n annot ctx = addToContext True n annot (varLvl (lastLvl ctx.size)) ctx

-- Typechecking has access to metas
interface (Monad m) => HasTc m where
  -- Explicit instance of metas so that the resolution doesn't die..
  metas : HasMetas (const m)

  -- Throw a typechecking error
  tcError : Context ns -> TcErrorAt ns -> m a

  -- Set the current typechecking location in the source file
  enterLoc : Loc -> m a -> m a

  -- Add a user goal
  addGoal : Name -> Expr ns -> Context ns -> m ()

  -- Get all the goals that have been seen
  getGoals : m (SnocList Goal)

-- This is the type over which we build the typechecking combinators.
--
-- `TcOp m md ns` is a typechecking operation in mode md.
--
-- It can be executed to produce an elaborated expression, depending on what `md` is.
0 TcOp : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcOp Check m ms = Annot ms -> m (Atom ms)
TcOp Infer m ms = (s : Maybe Stage) -> m (ExprAtMaybe s ms)

-- Typechecking in a specific context
0 TcAt : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcAt md m ns = Context ns -> TcOp md m ns

-- Typechecking in any context
--
-- This is what is mostly used to work with, since a lot of the time we don't know which
-- context we will check in ahead of time (due to things like inserted lambdas).
0 Tc : (md : TcMode) -> (0 m : Type -> Type) -> Type
Tc md m = forall ns . TcAt md m ns

-- Map a parametric monadic operation over Tc.
public export
intercept : HasTc m => (forall a . m a -> m a) -> {md : TcMode} -> Tc md m -> Tc md m
intercept f {md = Check} x = \ctx, as => f (x ctx as)
intercept f {md = Infer} x = \ctx, s => f (x ctx s)

-- Some useful shorthands

resolve : HasTc m => Val ns -> m (Val ns)
resolve x = resolveGlueAndMetas {sm = SolvingAllowed} @{metas} x

evaluate : Eval Val term value => Context ns -> term ns -> value ns
evaluate ctx t = eval ctx.defs t

promoteWithoutDefs : Size ns -> {d : Domain} -> Term d ns -> Atom ns
promoteWithoutDefs s {d = Syntax} tm = Choice tm (eval id tm)
promoteWithoutDefs s {d = Value} val = Choice (quote val) val

-- Create a fresh metavariable
freshMeta : HasTc m => Context ns -> Annot ns -> m (Atom ns)
freshMeta ctx (MkAnnot ty sort s) = do -- @@Todo: use type
  m <- newMeta {sm = SolvingAllowed} @{metas}
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure . promote $ SimpApps (ValMeta m $$ snd ctx.binds)

-- Insert all lambdas implicit lambdas in a type-directed manner, without regard
-- for what the expression is.
insertAll : (HasTc m) => Context ns -> m (Expr ns) -> m (Expr ns)

-- Insert all lambdas implicit lambdas in a type-directed manner, unless the given expression is a
-- matching implicit lambda.
insert : (HasTc m) => Context ns -> m (Expr ns) -> m (Expr ns)

-- Stage-aware `insert`.
insertAt : (HasTc m) => Context ns -> (s : Stage) -> m (ExprAt s ns) -> m (ExprAt s ns)

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
unify ctx a b = unify {sm = SolvingAllowed} @{unifyValues @{metas}} a.val b.val >>= \case
  AreSame => pure ()
  failure => tcError ctx $ WhenUnifying a b failure

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
check : HasTc m => Tc Infer m -> Tc Check m
check f = \ctx, annot => do
  result <- insertAt ctx annot.stage $ f ctx (Just annot.stage)
  unify ctx annot.ty result.annot.ty
  pure result.tm
  
-- Create a `SortData` instance for the given stage and sort kind, by instantiating metas
-- for the unknown information (byte sizes).
freshSortData : HasTc m => Context ns -> (s : Stage) -> (k : SortKind s) -> m (SortData s k ns)
freshSortData ctx Mta k = pure $ MtaSort 
freshSortData ctx Obj Dyn = do
  b <- freshMeta ctx psBytesAnnot
  pure $ ObjSort Dyn b
freshSortData ctx Obj Sized = do
  b <- freshMeta ctx staBytesAnnot
  pure $ ObjSort Sized b
  
-- Create a fresh annotation for the given stage and sort kind.
freshMetaAnnot : HasTc m => Context ns -> (s : Stage) -> SortKind s -> m (AnnotAt s ns)
freshMetaAnnot ctx s k = do
  tySort <- freshSortData ctx s k <&> .asAnnot
  ty <- freshMeta ctx (packStage tySort)
  pure $ MkAnnotAt ty tySort.ty
  
-- Fit the given annotation to the given kind.
fitAnnot : HasTc m => Context ns -> (s : Stage) -> (k : SortKind s) -> (annotTy ns, AtomTy ns) -> m (AnnotFor s k annotTy ns)
fitAnnot ctx s k (vty, univ) = do
  d <- freshSortData ctx s k
  unify ctx univ d.asAnnot.ty
  pure $ MkAnnotFor d vty
      
-- Create a lambda expression with the given data.
lamExpr : Context ns
  -> (piStage : Stage)
  -> (piIdent : Ident)
  -> (lamIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (AtomBody piIdent) ns)
  -> (body : AtomBody lamIdent ns)
  -> (ExprAt piStage ns)
lamExpr ctx piStage piIdent lamIdent bindAnnot bodyAnnot body =
  case piStage of
    Mta => do
      let MkAnnotFor MtaSort bindTy = bindAnnot
      let MkAnnotFor MtaSort bodyClosure = bodyAnnot
      MkExprAt
        (promote $ sMtaLam lamIdent body.open.syn)
        (forgetStage $ (promote $ vMtaPi piIdent bindTy.val bodyClosure.val)
          `asTypeIn` mtaTypeAnnot)
    Obj => do
      let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot
      let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot
      MkExprAt
        (promote $ sObjLam lamIdent ba.syn bb.syn body.open.syn)
        (forgetStage $ (promote $ vObjPi piIdent ba.val bb.val bindTy.val bodyClosure.val)
          `asTypeIn` sizedObjTypeAnnot (Choice ptrBytes ptrBytes))

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
  s <- subject (bind piIdent (packStage bindAnnot.asAnnot) ctx)
        (bodyAnnot.inner.open `asTypeIn` (wkS $ typeOfTypeAnnot piStage))
  pure $ lamExpr ctx piStage piIdent piIdent bindAnnot bodyAnnot (close ctx.defs s)
  
-- Infer the given object as a type, also inferring its stage in the process.
inferAnnot : HasTc m => Context ns -> (k : forall s . SortKind s) -> Tc Infer m -> m (s ** AnnotFor s k Atom ns)
inferAnnot ctx kind ty = do
  MkExpr t (MkAnnot univ _ stage) <- ty ctx Nothing
  res <- fitAnnot ctx stage kind {annotTy = AtomTy} (t, univ)
  pure (stage ** res)

-- Introduce a metavariable
tcMeta : HasTc m => {md : TcMode} -> {default Nothing name : Maybe Name} -> Tc md m
tcMeta {md = Check} {name} = \ctx, annot => do
  mta <- freshMeta ctx annot
  whenJust name $ \n => addGoal n (MkExpr mta annot) ctx
  pure mta
tcMeta {md = Infer} {name} = ensureKnownStage $ \ctx, stage => do
  annot <- freshMetaAnnot ctx stage Dyn -- remember, sized < dyn
  mta <- freshMeta ctx (packStage annot)
  whenJust name $ \n => addGoal n (MkExpr mta (packStage annot)) ctx
  pure $ MkExprAt mta annot

-- Form a pi type
tcPi : HasTc m
  => Ident
  -> Tc Infer m
  -> Tc Check m
  -> Tc Infer m
tcPi x a b = ensureKnownStage $ \ctx, stage => case stage of
  -- @@Reconsider: Kovacs infers the stage from the domain if it is not given..
  -- This is more annoying here because of byte metas, but also I am not
  -- convinced that it is the right thing to do. It might lead to some weird elab results.
  Mta => do
    let aSort = mtaTypeAnnot
    a' <- check a ctx aSort
    b' <- b (bind x (a' `asTypeIn` aSort) ctx) (wkS mtaTypeAnnot)
    pure $ MkExprAt (promote $ sMtaPi x a'.syn b'.syn) (forgetStage mtaTypeAnnot)
  Obj => do
    ba <- freshMeta ctx staBytesAnnot
    bb <- freshMeta ctx staBytesAnnot
    let aSort = sizedObjTypeAnnot ba
    a' <- check a ctx aSort
    b' <- b (bind x (a' `asTypeIn` aSort) ctx) (wkS $ sizedObjTypeAnnot bb)
    pure $ MkExprAt
      (promote $ sObjPi x ba.syn bb.syn a'.syn b'.syn)
      (forgetStage $ sizedObjTypeAnnot (Choice ptrBytes ptrBytes)) -- @@Todo: clean this Choice up

-- The type of the callback that `ifForcePi` calls when it finds a matching
-- type.
0 ForcePiCallback : (r : Type) -> Stage -> Ctx -> Type
ForcePiCallback r stage ns = (resolvedPi : AtomTy ns)
  -> (piIdent : Ident)
  -> (a : AnnotFor stage Sized Atom ns)
  -> (b : AnnotFor stage Sized (AtomBody piIdent) ns)
  -> r

-- Given a `potentialPi`, try to match it given that we expect something in
-- `mode` and `stage`.
--
-- If it matches, call `ifMatching` with the appropriate information, otherwise
-- call `ifMismatching` with the appropriate information.
ifForcePi : (HasTc m) => Context ns
  -> (ident : Ident)
  -> (stage : Stage)
  -> (potentialPi : AtomTy ns)
  -> (ifMatching : ForcePiCallback (m r) stage ns)
  -> (ifMismatching : (stage' : Stage) -> ForcePiCallback (m r) stage' ns)
  -> m r
ifForcePi ctx (mode, name) stage potentialPi ifMatching ifMismatching
  = resolve potentialPi.val >>= \case
    -- object-level pi
    resolvedPi@(RigidBinding piStage@Obj (Bound _ (BindObjPi (piMode, piName) ba bb a) b)) => 
      let res = case decEq (piMode, piStage) (mode, stage) of
            Yes Refl => ifMatching 
            _ => ifMismatching Obj
      in let
        ba' = promote ba
        bb' = promote bb
      in res (promote resolvedPi) (piMode, piName)
          (MkAnnotFor (ObjSort Sized ba') (promote a))
          (MkAnnotFor (ObjSort Sized bb') (promoteBody b))
    -- meta-level pi
    resolvedPi@(RigidBinding piStage@Mta (Bound _ (BindMtaPi (piMode, piName) a) b)) =>
      let res = case decEq (piMode, piStage) (mode, stage) of
            Yes Refl => ifMatching
            _ => ifMismatching Mta
      in res (promote resolvedPi) (piMode, piName)
          (MkAnnotFor MtaSort (promote a))
          (MkAnnotFor MtaSort (promoteBody b))
    resolvedPi => do
      -- Did not get a pi, try to construct a pi based on the info we have and
      -- unify it with the potential pi.
      MkExprAt createdPi _ <- tcPi (mode, name) (tcMeta {md = Infer}) (tcMeta {md = Check}) ctx (Just stage)
      unify ctx (promote resolvedPi) createdPi
      ifForcePi ctx (mode, name) stage createdPi ifMatching ifMismatching

-- Typechecking combinator for lambdas.
tcLam : HasTc m => (md : TcMode)
  -> (n : Ident)
  -> (bindTy : Maybe (Tc Infer m))
  -> (body : Tc md m)
  -> Tc md m
tcLam Check lamIdent bindTy body = \ctx, annot@(MkAnnot ty sort stage) => do
  -- We must check that the type we have is a pi
  ifForcePi ctx lamIdent stage ty
    (\resolvedPi, piIdent, a, b => do
      -- Great, it is a pi. Now first reconcile this with the annotation type
      -- of the lambda.
      whenJust bindTy $ \bindTy' => do
        MkExprAt bindPi _ <- tcPi lamIdent bindTy' (tcMeta {md = Check}) ctx (Just stage)
        unify ctx resolvedPi bindPi

      -- Then check the body with the computed annotation type.
      body' <- body
        (bind lamIdent (packStage a.asAnnot) ctx)
        (packStage b.open.asAnnot)
      
      -- Produce the appropriate lambda based on the stage.
      pure $ (lamExpr ctx stage piIdent lamIdent a b (close ctx.defs body')).tm
    )
    (\piStage, resolvedPi, piIdent, a, b => case fst piIdent of
      -- It wasn't the right kind of pi; if it was implicit, insert a lambda
      Implicit => do
        MkExprAt tm _ <- insertLam ctx piStage piIdent a b (tcLam Check lamIdent bindTy body)
        pure tm
      -- Otherwise, we have the wrong kind of pi.
      _ => tcError ctx (WrongPiMode (fst piIdent) resolvedPi)
    )
tcLam Infer lamIdent bindTy body = ensureKnownStage $ \ctx, stage => do
  -- @@Reconsider: Same remark as for pis.
  -- We have a stage, but no type, so just instantiate a meta..
  annot <- freshMetaAnnot ctx stage Sized
  res <- tcLam Check lamIdent bindTy (check body) ctx (packStage annot)
  pure $ MkExprAt res annot

-- Infer a tuple, given by a list of named terms
tcTuple : HasTc m => List (Ident, Tc Check m) -> Tc Check m

-- Infer a variable, by looking up in the context
tcVar : HasTc m => Name -> Tc Infer m
tcVar n = \ctx, stage' => case lookup ctx n of
    Nothing => tcError ctx $ UnknownName n
    Just idx => do
      let tm = promote $ varIdx idx
      let ty = promote $ ctx.con.index idx
      let sort = promote $ ctx.sorts.index idx
      let stage = ctx.stages.index idx
      adjustStageIfNeeded ctx (MkExpr tm (MkAnnot ty sort stage)) stage'

-- Infer or check a user-supplied hole
--
-- We should at least know the stage of the hole. User holes are added to the
-- list of goals, which can be displayed after typechecking.
tcHole : HasTc m => {md : TcMode} -> Maybe Name -> Tc md m
tcHole {md} name = tcMeta {md} {name = name}

-- Check a spine against a telescope.
--
-- Returns the checked spine and the remaining terms in the input.
checkSpine : HasTc m
  => Context ns
  -> List (Ident, Tc Check m)
  -> Tel ar Annot ns
  -> m (AtomSpine ar ns, List (Ident, Tc Check m))
checkSpine ctx tms [] = pure ([], tms)
checkSpine ctx [] annots = ?gaga
checkSpine ctx ((name, tm) :: tms) (annot :: annots) = do
  tm' <- tm ctx annot 
  (tms', rest) <- checkSpine ctx tms ?annots
  ?fafafaj
  -- pure (tm' :: sub (ctx.defs :< tm'.val) tms', rest)

tcApp : HasTc m
  => (subject : Expr ns)
  -> List (Ident, Tc Check m)
  -> Tc Infer m

tcPrim : HasTc m
  => {r : PrimitiveReducibility}
  -> {k : PrimitiveClass}
  -> Primitive k r ar
  -> List (Ident, Tc Check m)
  -> Tc Infer m
tcPrim p args = \ctx, stage => do
  let (pParams, pRet) = primTy p
  ?qjqjqj
  -- (sp, rest) <- checkSpine ?args ?pParams
  -- let ret = promote ctx $ eval (ctx.defs ::< mapSpine (\v => force v.val) sp) pRet.ty.syn
  -- let retSort = promote ctx $ eval (ctx.defs ::< mapSpine (\v => force v.val) sp) pRet.sort.syn
  -- tcApp (MkExpr (promote ctx $ sPrim p (mapSpine (\v => force v.syn) sp)) (MkAnnot ret retSort pRet.stage)) rest ctx stage


-- @@TODO:
--
-- fix lambdas
-- Let
-- Let rec
-- Universe
-- Sigma
-- Pairs
-- Projection
-- Literals
-- Coercion
