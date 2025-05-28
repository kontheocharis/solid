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
  binds : Exists (\ar => Spine ar (ValTy) ns)

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

reify : Context ns -> Val ns -> Tm ns
reify ctx v = quote ctx.size v
  
promote : Context ns -> {d : Domain} -> Term d ns -> Atom ns
promote ctx {d = Syntax} tm = Choice tm (evaluate ctx tm) 
promote ctx {d = Value} val = Choice (reify ctx val) val

promoteWithoutDefs : Size ns -> {d : Domain} -> Term d ns -> Atom ns
promoteWithoutDefs s {d = Syntax} tm = Choice tm (eval (id s) tm)
promoteWithoutDefs s {d = Value} val = Choice (quote s val) val

weaken : WeakSized value => Context ns -> value ns -> value (ns :< n)
weaken ctx = weakS (SS ctx.size) ctx.size (Drop Id)

-- Annotation versions of syntax
  
-- The type of types, for the given stage.
-- 
-- For the meta level, this is TYPE
-- For the object level, this is Type 0.
public export
typeOfTypeAnnot : Context ns -> Stage -> Annot ns
typeOfTypeAnnot ctx stage = let t = promote ctx $ typeOfTypesForStage stage in MkAnnot t t stage

-- TYPE as an annotation
public export
mtaTypeAnnot : Context ns -> Annot ns
mtaTypeAnnot ctx = let t = promote ctx mtaType in MkAnnot t t Mta

-- Dyn b as an annotation
public export
dynObjTypeAnnot : Context ns -> Atom ns -> Annot ns
dynObjTypeAnnot ctx b = MkAnnot --@@Todo: more performant
  (promote ctx $ dynObjType b.syn)
  (promote ctx $ sizedObjType zeroBytes)
  Obj

-- Type b as an annotation
public export
sizedObjTypeAnnot : Context ns -> Atom ns -> Annot ns
sizedObjTypeAnnot ctx b = MkAnnot --@@Todo: more performant
  (promote ctx $ sizedObjType b.syn)
  (promote ctx $ sizedObjType zeroBytes)
  Obj

-- Partially static bytes, the argument to Dyn
public export
psBytesAnnot : Context ns -> Annot ns
psBytesAnnot ctx = MkAnnot (promote ctx psBytes) (promote ctx mtaType) Mta

-- Static bytes, the argument to Type
public export
staBytesAnnot : Context ns -> Annot ns
staBytesAnnot ctx = MkAnnot (promote ctx staBytes) (promote ctx mtaType) Mta

-- Create a fresh metavariable
freshMeta : HasTc m => Context ns -> Annot ns -> m (Atom ns)
freshMeta ctx (MkAnnot ty sort s) = do -- @@Todo: use type
  m <- newMeta {sm = SolvingAllowed} @{metas}
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure . promote ctx $ SimpApps (ValMeta m $$ snd ctx.binds)

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
unify ctx a b = unify {sm = SolvingAllowed} @{unifyValues @{metas}} ctx.size a.val b.val >>= \case
  AreSame => pure ()
  failure => tcError ctx $ WhenUnifying a b failure

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
check : HasTc m => Tc Infer m -> Tc Check m
check f = \ctx, annot => do
  result <- insertAt ctx annot.stage $ f ctx (Just annot.stage)
  unify ctx annot.ty result.annot.ty
  pure result.tm

-- Evaluate a closure with a extended environment
evalClosure : Context ns -> Body Value n ns -> Term Value (ns :< n')
evalClosure ctx (Closure env body) = eval (lift ctx.size env) body

-- Promote a closure to a function on atoms.
promoteClosure : Context ns -> Body Value n ns -> (Atom (ns :< n) -> Atom (ns :< n))
promoteClosure ctx (Closure env body) v
  = promoteWithoutDefs (SS ctx.size) $ eval {val = Term Value} (env . Drop Id :< v.val) body

-- Close a syntactic term into a closure.
public export
close : Context ns -> Tm (ns :< n) -> Body Value n ns
close ctx ty = Closure (id ctx.size) ty

-- The last variable.
public export
here : Context ns -> Atom (ns :< n)
here ctx = Choice (varIdx IZ) (here {tm = Term Value} ctx.size)
  
-- Whether an annotation is sized or dynamic.
data AnnotKind : Type where
  Dyn : AnnotKind
  Sized : AnnotKind
  
-- For a given stage and annotation kind, this holds the data of the annotation.
data AnnotFor : Stage -> AnnotKind -> (annotTy : Ctx -> Type) -> Ctx -> Type where
  -- A meta-level annotation does not need any size.
  MtaAnnot : (ty : annotTy ns) -> AnnotFor Mta k annotTy ns
  -- A dynamic object annotation has a partially-static size.
  DynObjAnnot : (by : Atom ns) -> (ty : annotTy ns) -> AnnotFor Obj Dyn annotTy ns
  -- A sized object annotation has a static size.
  SizedObjAnnot : (by : Atom ns) -> (ty : annotTy ns) -> AnnotFor Obj Sized annotTy ns
  
-- Extract the inner type of an annotation.
(.inner) : AnnotFor s k annotTy ns -> annotTy ns
(.inner) (MtaAnnot ty) = ty
(.inner) (DynObjAnnot _ ty) = ty
(.inner) (SizedObjAnnot _ ty) = ty
  
-- Forget about the kind of an annotation.
public export
asAnnotAt : Context ns -> AnnotFor s k AtomTy ns -> AnnotAt s ns
asAnnotAt ctx (MtaAnnot ty) = forgetStage $ ty `asTypeIn` mtaTypeAnnot ctx
asAnnotAt ctx (DynObjAnnot by ty) = forgetStage $ ty `asTypeIn` dynObjTypeAnnot ctx by
asAnnotAt ctx (SizedObjAnnot by ty) = forgetStage $ ty `asTypeIn` sizedObjTypeAnnot ctx by

public export
asBodyAnnotAt : Context ns -> AnnotFor s k (Body Value n) ns -> AnnotAt s (ns :< n')
asBodyAnnotAt ctx (MtaAnnot ty) = forgetStage $ promoteWithoutDefs (SS ctx.size) (evalClosure ctx ty) `asTypeIn` (weaken ctx $ mtaTypeAnnot ctx)
asBodyAnnotAt ctx (DynObjAnnot by ty) = forgetStage $ promoteWithoutDefs (SS ctx.size) (evalClosure ctx ty) `asTypeIn` (weaken ctx $ dynObjTypeAnnot ctx by)
asBodyAnnotAt ctx (SizedObjAnnot by ty) = forgetStage $ promoteWithoutDefs (SS ctx.size) (evalClosure ctx ty) `asTypeIn` (weaken ctx $ sizedObjTypeAnnot ctx by)

annotSort : Context ns -> AnnotFor s k annotTy ns -> AnnotAt s ns
annotSort ctx (MtaAnnot _) = forgetStage $ mtaTypeAnnot ctx
annotSort ctx (DynObjAnnot by _) = forgetStage $ dynObjTypeAnnot ctx by
annotSort ctx (SizedObjAnnot by _) = forgetStage $ sizedObjTypeAnnot ctx by
  
-- Fit the given annotation to the given kind.
fitAnnot : HasTc m => Context ns -> (k : AnnotKind) -> (s : Stage) -> (annotTy ns, AtomTy ns) -> m (AnnotFor s k annotTy ns)
fitAnnot ctx kind stage (vty, univ) =
  case stage of
    Mta => do
      unify ctx univ (mtaTypeAnnot ctx).ty
      pure $ MtaAnnot vty
    Obj => case kind of
      Dyn => do 
        b <- freshMeta ctx (psBytesAnnot ctx)
        unify ctx univ (dynObjTypeAnnot ctx b).ty
        pure $ DynObjAnnot b vty
      Sized => do
        b <- freshMeta ctx (staBytesAnnot ctx)
        unify ctx univ (sizedObjTypeAnnot ctx b).ty
        pure $ SizedObjAnnot b vty
      
-- Create a lambda expression with the given data.
lamExpr : Context ns
  -> (piStage : Stage)
  -> (piIdent : Ident)
  -> (lamIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (Body Value piIdent) ns)
  -> (body : Atom (ns :< lamIdent))
  -> (ExprAt piStage ns)
lamExpr ctx piStage piIdent lamIdent bindAnnot bodyAnnot body =
  case piStage of
    Mta => do
      let MtaAnnot bindTy = bindAnnot
      let MtaAnnot bodyClosure = bodyAnnot
      MkExprAt
        (promote ctx $ sMtaLam lamIdent body.syn)
        (forgetStage $ (promote ctx $ vMtaPi piIdent bindTy.val bodyClosure)
          `asTypeIn` mtaTypeAnnot ctx)
    Obj => do
      let SizedObjAnnot ba bindTy = bindAnnot
      let SizedObjAnnot bb bodyClosure = bodyAnnot
      MkExprAt
        (promote ctx $ sObjLam lamIdent ba.syn bb.syn body.syn)
        (forgetStage $ (promote ctx $ vObjPi piIdent ba.val bb.val bindTy.val bodyClosure)
          `asTypeIn` sizedObjTypeAnnot ctx (Choice ptrBytes ptrBytes))

-- Insert (some kind of an implicit) lambda from the given information.
--
-- This adds the binder to the subject and `recurses`, yielding a lambda with the
-- given Pi type.
insertLam : HasTc m => Context ns
  -> (piStage : Stage)
  -> (piIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (Body Value piIdent) ns)
  -> (subject : Tc Check m)
  -> m (ExprAt piStage ns)
insertLam ctx piStage piIdent bindAnnot bodyAnnot subject = do
  s <- subject (bind piIdent (packStage (asAnnotAt ctx bindAnnot)) ctx)
        (promoteClosure ctx bodyAnnot.inner (here ctx) `asTypeIn` (weaken ctx $ typeOfTypeAnnot ctx piStage))
  pure $ lamExpr ctx piStage piIdent piIdent bindAnnot bodyAnnot s
  
-- Infer the given object as a type, also inferring its stage in the process.
inferAnnot : HasTc m => Context ns -> (k : AnnotKind) -> Tc Infer m -> m (s ** AnnotFor s k Atom ns)
inferAnnot ctx kind ty = do
  MkExpr t (MkAnnot univ _ stage) <- ty ctx Nothing
  res <- fitAnnot ctx kind stage {annotTy = AtomTy} (t, univ)
  pure (stage ** res)
  
freshMetaAnnot : HasTc m => Context ns -> (s : Stage) -> m (AnnotAt s ns)
freshMetaAnnot ctx s = do
  tySort <- freshMeta ctx (typeOfTypeAnnot ctx s)
  ty <- freshMeta ctx (MkAnnot tySort tySort s)
  pure $ MkAnnotAt ty tySort

-- Introduce a metavariable
tcMeta : HasTc m => {md : TcMode} -> {default Nothing name : Maybe Name} -> Tc md m
tcMeta {md = Check} {name} = \ctx, annot => do
  mta <- freshMeta ctx annot
  whenJust name $ \n => addGoal n (MkExpr mta annot) ctx
  pure mta
tcMeta {md = Infer} {name} = ensureKnownStage $ \ctx, stage => do
  annot <- freshMetaAnnot ctx stage
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
    let aSort = mtaTypeAnnot ctx
    a' <- check a ctx aSort
    b' <- b (bind x (a' `asTypeIn` aSort) ctx) (weaken ctx $ mtaTypeAnnot ctx)
    pure $ MkExprAt (promote ctx $ sMtaPi x a'.syn b'.syn) (forgetStage $ mtaTypeAnnot ctx)
  Obj => do
    ba <- freshMeta ctx (staBytesAnnot ctx)
    bb <- freshMeta ctx (staBytesAnnot ctx)
    let aSort = sizedObjTypeAnnot ctx ba
    a' <- check a ctx aSort
    b' <- b (bind x (a' `asTypeIn` aSort) ctx) (weaken ctx $ sizedObjTypeAnnot ctx bb)
    pure $ MkExprAt
      (promote ctx $ sObjPi x ba.syn bb.syn a'.syn b'.syn)
      (forgetStage $ sizedObjTypeAnnot ctx (Choice ptrBytes ptrBytes)) -- @@Todo: clean this Choice up

-- The type of the callback that `ifForcePi` calls when it finds a matching
-- type.
0 ForcePiCallback : (r : Type) -> Stage -> Ctx -> Type
ForcePiCallback r stage ns = (resolvedPi : AtomTy ns)
  -> (piIdent : Ident)
  -> (a : AnnotFor stage Sized Atom ns)
  -> (b : AnnotFor stage Sized (Body Value piIdent) ns)
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
        ba' = promote ctx ba
        bb' = promote ctx bb
      in res (promote ctx resolvedPi) (piMode, piName) (SizedObjAnnot ba' (promote ctx a)) (SizedObjAnnot bb' b)
    -- meta-level pi
    resolvedPi@(RigidBinding piStage@Mta (Bound _ (BindMtaPi (piMode, piName) a) b)) =>
      let res = case decEq (piMode, piStage) (mode, stage) of
            Yes Refl => ifMatching
            _ => ifMismatching Mta
      in res (promote ctx resolvedPi) (piMode, piName) (MtaAnnot (promote ctx a)) (MtaAnnot b)
    resolvedPi => do
      -- Did not get a pi, try to construct a pi based on the info we have and
      -- unify it with the potential pi.
      MkExprAt createdPi _ <- tcPi (mode, name) (tcMeta {md = Infer}) (tcMeta {md = Check}) ctx (Just stage)
      unify ctx (promote ctx resolvedPi) createdPi
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
      body' <- body (bind lamIdent (packStage $ asAnnotAt ctx a) ctx) (packStage $ asBodyAnnotAt ctx b)
      
      -- Produce the appropriate lambda based on the stage.
      pure $ (lamExpr ctx stage piIdent lamIdent a b body').tm
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
  annot <- freshMetaAnnot ctx stage
  res <- tcLam Check lamIdent bindTy (check body) ctx (packStage annot)
  pure $ MkExprAt res annot

-- Infer a tuple, given by a list of named terms
tcTuple : HasTc m => List (Ident, Tc Check m) -> Tc Check m

-- Infer a variable, by looking up in the context
tcVar : HasTc m => Name -> Tc Infer m
tcVar n = \ctx, stage' => case lookup ctx n of
    Nothing => tcError ctx $ UnknownName n
    Just idx => do
      let tm = promote ctx $ varIdx idx
      let ty = promote ctx $ ctx.con.index idx
      let sort = promote ctx $ ctx.sorts.index idx
      let stage = ctx.stages.index idx
      adjustStageIfNeeded ctx (MkExpr tm (MkAnnot ty sort stage)) stage'

-- Infer or check a user-supplied hole
--
-- We should at least know the stage of the hole. User holes are added to the
-- list of goals, which can be displayed after typechecking.
tcHole : HasTc m => {md : TcMode} -> Maybe Name -> Tc md m
tcHole {md} name = tcMeta {md} {name = name}

checkSpine : HasTc m
  => List (Ident, Tc Check m)
  -> Tel ar Annot ns
  -> m (Spine ar Atom ns, List (Ident, Tc Check m))


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
  (sp, rest) <- checkSpine args pParams
  let ret = promote ctx $ eval (ctx.defs ::< mapSpine (\v => force v.val) sp) pRet.ty.syn
  let retSort = promote ctx $ eval (ctx.defs ::< mapSpine (\v => force v.val) sp) pRet.sort.syn
  tcApp (MkExpr (promote ctx $ sPrim p (mapSpine (\v => force v.syn) sp)) (MkAnnot ret retSort pRet.stage)) rest ctx stage


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
