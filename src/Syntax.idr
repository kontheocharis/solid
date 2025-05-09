module Syntax

import Utils
import Context

%default total

-- A metavariable is just a string name
public export
record MetaVar where
  name : String

-- The stage we are in
--
-- This is a two-level language.
public export
data Stage = Obj | Mta

-- Whether an expression head is reducible
--
-- Remembers the stage at which it is reducible
-- For now this is uniform over stages.
public export
data Reducibility : Stage -> Type where
  -- Reducible because it is callable with an argument.
  Callable : Reducibility s

  -- Reducible because it is a lazy value, it can be forced (but has currently
  -- not been).
  Unforced : Reducibility s
  -- Irreducible, i.e. rigid.
  Rigid : Reducibility s

-- Whether we are talking about syntax or values.
--
-- They differ primarily in their representation of open terms. Syntax just uses
-- de-Brujin indices, while Value works like a defunctionalised HOAS, storing
-- some syntax and an environment to evaluate in.
public export
data Domain = Syntax | Value

-- Terms are indexed by domain, rather than having two separate classes.
--
-- They are also indexed by contexts, making them well-scoped.
public export
data Term : Domain -> Ctx -> Type

-- Terms can be evalued and quoted (given later)
public export
Eval (Term Value) (Term Syntax) (Term Value)

public export
Quote (Term Value) (Term Syntax)

public export
Thin (Term Value)

-- Primitives are either neutral or normal.
--
-- Neutral primitives might still be applied to other arguments after being fully
-- applied to their arity. For example,
--
-- ifThenElse : (A : Type) -> Bool -> A -> A -> A
--
-- is a primitive of arity 4, but could be applied to more than 2 arguments,
-- for example if we instantiate A with a function type:
--
-- Conversely, normal primitives can never be applied to more arguments than their
-- arity.
public export
data PrimitiveClass = PrimNeu | PrimNorm

-- The theory of primitives.
--
-- These essentially form a Lawvere theory, though the equations are given
-- separately later (they are the reduction rules). They will also be given
-- proper types later.
public export
data Primitive : PrimitiveClass -> Arity -> Type

-- This is a fully applied term for some operator in a theory.
--
-- Used to represent fully applied primitives.
public export
data Applied : (Arity -> Type) -> Domain -> Ctx -> Type where
  ($$) : k as -> Spine as (Term d) ns -> Applied k d ns

export infixr 5 $$

-- Here we will give the reduction rules of primitives (later)
public export
Eval (Term Value) (Applied (Primitive k) Syntax) (Term Value)

public export
Quote (Applied f Value) (Applied f Syntax) where
  quote s (h $$ sp) = h $$ quote s sp

public export
Thin (Applied f Value) where
  thin e (h $$ sp) = h $$ thin e sp

-- The list of binders in the language, indexed by stage.
--
-- Each of these might carry some data.
public export
data Binder : (s : Stage) -> Reducibility s -> Domain -> Ctx -> Type where
  -- Meta or object-level lambda
  BindLam : Binder s Callable d ns

  -- Meta or object-level let
  BindLet : (rhs : Term d ns) -> Binder s Unforced d ns

  -- Meta or object-level pi
  BindPi : (dom : Term d ns) -> Binder s Rigid d ns

-- Binder is a functor
mapBinder : (Term d ns -> Term d' ms) -> Binder md r d ns -> Binder md r d' ms
mapBinder _ BindLam = BindLam
mapBinder f (BindLet t) = BindLet (f t)
mapBinder f (BindPi t) = BindPi (f t)

public export
Eval over (Term d) (Term d') => Eval over (Binder md r d) (Binder md r d') where
  eval env b = mapBinder (eval env) b

public export
Quote (Term d) (Term d') => Quote (Binder md r d) (Binder md r d') where
  quote s b = mapBinder (quote s) b

public export
Thin (Term d) => Thin (Binder md r d) where
  thin e b = mapBinder (thin e) b

-- Variables are de-Brujin indices or levels depending on if we are in value or
-- syntax ~> fast variable lookup during evaluation, and free weakening for
-- values.
public export
data Variable : Domain -> Ctx -> Type where
  Level : Lvl ns -> Variable Value ns
  Index : Idx ns -> Variable Syntax ns

-- A body is basically a term under a binder.
--
-- Either a term with a free variable or a (defunctionalised) delayed
-- evaluation.
public export
data Body : Domain -> Name -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term Value) ms -> Term Syntax (ms :< n) -> Body Value n ns

-- Helper to package a binder with its body.
public export
data Thunk : (s : Stage) -> Reducibility s -> Domain -> Ctx -> Type where
  Bound : (s : Stage) -> {0 r : Reducibility s}
      -> (n : Name) -> Binder s r d ns -> Body d n ns -> Thunk s r d ns

-- Every callable thunk can be applied to a term.
public export
callThunk : Thunk s Callable Value ns -> Term Value ns -> Term Value ns
callThunk (Bound s n BindLam (Closure env body)) arg = eval (env :< arg) body

-- Every unforced thunk can be forced.
public export
forceThunk : Thunk s Unforced Value ns -> Term Value ns
forceThunk (Bound s n (BindLet v) (Closure env body)) = eval (env :< v) body

-- Different spine heads, meaning x in `x a1 ... an`, are reduced
-- to different extents.
--
-- Unification might have to look at simplified heads, but code extraction only
-- needs normalised heads. I.e. we never reduce object thunks unless we have to.
public export
data HeadKind : Domain -> Type where
  -- Anything goes in syntax
  NA : HeadKind Syntax
  -- A merely normalised head. This might be unforced.
  Normalised : HeadKind Value
  -- A fully simplified head, fully forced.
  Simplified : HeadKind Value

public export
data Head : (d : Domain) -> HeadKind d -> Ctx -> Type where
  -- Variables and metas are simplified if they are values
  SynVar : Variable Syntax ns -> Head Syntax NA ns
  ValVar : Variable Value ns -> Head Value Simplified ns
  SynMeta : MetaVar -> Head Syntax NA ns
  ValMeta : MetaVar -> Head Value Simplified ns

  -- A syntactic thunk
  SynThunk : (s : Stage) -> (r : Reducibility s) -> Thunk s r Syntax ns -> Head Syntax NA ns

  -- Meta-level callable thunks cannot appear as heads in values.
  --
  -- Thus, all we have are object-level thunks (which are merely normalised because
  -- they can technically be more simplified)
  ObjCallable : Thunk Obj Callable Value ns -> Head Value Normalised ns
  ObjLazy : Thunk Obj Unforced Value ns -> Head Value Normalised ns

  -- An applied primitive can only be a head if it is neutral.
  PrimNeutral : Applied (Primitive PrimNeu) d ns -> Head d e ns

-- Head applied to a spine.
namespace HeadApplied
  public export
  data HeadApplied : (d : Domain) -> HeadKind d -> Ctx -> Type where
    ($$) : Head d hk ns -> Spine as (Term d) ns -> HeadApplied d hk ns

public export
data Term where
  -- Spine applied to syntactic head
  SynApps : HeadApplied Syntax NA ns -> Term Syntax ns

  -- Spine applied to a normalised value head
  --
  -- Also stores the fully simplified form lazily (glued eval trick)
  -- This makes unification much faster in some cases. It also allows us
  -- to extract either normalised or simplified syntax during quoting.
  GluedApps : HeadApplied Value Normalised ns -> Lazy (Term Value ns) -> Term Value ns

  -- Spine applied to a simplified value head
  --
  -- Cannot be reduced further
  SimpApps : HeadApplied Value Simplified ns -> Term Value ns

  -- Callable meta thunk, never applied to a spine
  MtaCallable : Thunk Mta Callable Value ns -> Term Value ns

  -- Callable object thunk that must be simplified if applied to anything.
  --
  -- If it shouldn't be simplified it should be a GluedApps (ObjCallable ..) instead.
  SimpObjCallable : Thunk Obj Callable Value ns -> Term Value ns

  -- Rigid thunk, never applied.
  RigidThunk : Thunk s Rigid d ns -> Term d ns

  -- Normal primitive, never applied.
  PrimNormal : Applied (Primitive PrimNorm) d ns -> Term d ns

-- Values support free thinning
-- public export
-- Thin (Term Value)

-- Evaluation and quoting for all the syntax:

public export
Eval (Term Value) (Variable Syntax) (Term Value) where
  eval (env :< e) (Index IZ) = e
  eval (env :< e) (Index (IS i)) = eval env (Index i)
  eval [<] (Index _) impossible

public export
Quote (Variable Value) (Variable Syntax) where
  quote s (Level l) = Index (quote s l)

public export
Thin (Variable Value) where
  thin s (Level l) = Level (thin s l)

public export
Vars (Term Value) where
  here s = SimpApps (ValVar (Level (lastLvl s)) $$ [])

public export
Eval (Term Value) (Body Syntax n) (Body Value n) where
  eval env (Delayed t) = Closure env t

public export
Quote (Body Value n) (Body Syntax n) where
  quote s (Closure env t) = Delayed (quote {val = Term Value} (SS s) (eval (lift s env) t))

public export
Thin (Body Value n) where
  thin e (Closure env t) = Closure (env . e) t

public export
Eval (Term Value) (Thunk s r Syntax) (Thunk s r Value) where
  eval env (Bound s n bind body) = Bound s n (eval env bind) (eval env body)

public export
Quote (Thunk s r Value) (Thunk s r Syntax) where
  quote s (Bound s' n bind body) = Bound s' n (quote s bind) (quote s body)

public export
Thin (Thunk s r Value) where
  thin s (Bound s' n bind body) = Bound s' n (thin s bind) (thin s body)

-- Helper to apply a value to a spine.
--
-- This is the only place where it could crash if there is a bug, because
-- the syntax is not well-typed (only well-scoped).
public export
apps : Term Value ns -> Spine as (Term Value) ns -> Term Value ns
apps (GluedApps (v $$ sp) gl) sp' = GluedApps (v $$ sp ++ sp') (apps gl sp')
apps (SimpApps (v $$ sp)) sp' = SimpApps (v $$ sp ++ sp')
apps (MtaCallable t) [] = MtaCallable t
apps (MtaCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (SimpObjCallable t) [] = SimpObjCallable t
apps (SimpObjCallable t) (x :: sp') = apps (callThunk t x) sp'
apps (RigidThunk _) _ = error "impossible"
apps (PrimNormal _) _ = error "impossible"

public export
Eval (Term Value) (Head Syntax NA) (Term Value) where
  eval env (SynVar v) = eval env v
  eval env (SynMeta v) = SimpApps (ValMeta v $$ [])
  eval env (SynThunk s Rigid t) = RigidThunk {s = s} (eval env t)
  eval env (SynThunk Obj Callable t) = GluedApps (ObjCallable (eval env t) $$ []) (SimpObjCallable (eval env t))
  eval env (SynThunk Obj Unforced t) = GluedApps (ObjLazy (eval env t) $$ []) (forceThunk {s = Obj} (eval env t))
  eval env (SynThunk Mta Callable t) = MtaCallable (eval env t)
  eval env (SynThunk Mta Unforced t) = forceThunk {s = Mta} (eval env t)
  eval env (PrimNeutral prim) = eval env prim

public export
Quote (Head Value hk) (Head Syntax NA) where
  quote s (ValVar v) = SynVar (quote s v)
  quote s (ValMeta m) = SynMeta m
  quote s (ObjCallable t) = SynThunk Obj Callable (quote s t)
  quote s (ObjLazy t) = SynThunk Obj Unforced (quote s t)
  quote s (PrimNeutral p) = PrimNeutral (quote s p)

public export
Thin (Head Value hk) where
  thin s (ValVar v) = ValVar (thin s v)
  thin s (ValMeta m) = ValMeta m
  thin s (ObjCallable t) = ObjCallable (thin s t)
  thin s (ObjLazy t) = ObjLazy (thin s t)
  thin s (PrimNeutral p) = PrimNeutral (thin s p)

public export
Quote (HeadApplied Value hk) (HeadApplied Syntax NA) where
  quote s (($$) {as = as} h sp) = ($$) {as = as} (quote s h) (quote s sp)

public export
Thin (HeadApplied Value hk) where
  thin e (h $$ sp) = thin e h $$ thin e sp

public export
Thin (Term Value) where
  thin e (GluedApps a f) = GluedApps (thin e a) (thin e f)
  thin e (SimpApps a) = SimpApps (thin e a)
  thin e (MtaCallable c) = MtaCallable (thin e c)
  thin e (SimpObjCallable c) = SimpObjCallable (thin e c)
  thin e (RigidThunk c) = RigidThunk (thin e c)
  thin e (PrimNormal p) = PrimNormal (thin e p)

public export covering
Eval (Term Value) (Term Syntax) (Term Value) where
  eval env (SynApps (($$) {as = as} h sp)) = apps {as = as} (eval env h) (eval env sp)
  eval env (RigidThunk {s = s} t) = RigidThunk {s = s} (eval env t)
  eval env (PrimNormal prim) = eval env prim

public export
Quote (Term Value) (Term Syntax) where
  quote s (GluedApps a _) = SynApps (quote s a)
  quote s (SimpApps a) = SynApps (quote s a)
  quote s (MtaCallable c) = SynApps (SynThunk Mta Callable (quote s c) $$ [])
  quote s (SimpObjCallable c) = SynApps (SynThunk Obj Callable (quote s c) $$ [])
  quote s (RigidThunk {s = s'} c) = RigidThunk {s = s'} (quote s c)
  quote s (PrimNormal p) = PrimNormal (quote s p)

-- Some convenient shorthands

public export
0 Tm : Ctx -> Type
Tm = Term Syntax

public export
0 Ty : Ctx -> Type
Ty = Tm

public export
0 Val : Ctx -> Type
Val = Term Value

public export
0 ValTy : Ctx -> Type
ValTy = Val

public export
0 Env : Ctx -> Ctx -> Type
Env ms ns = Sub ms Val ns

-- We can extend the variable search machinery to the syntax:

public export
var : (n : String) -> {auto prf : In n ns} -> Tm ns
var n {prf = prf} = SynApps (SynVar (Index (idx @{prf})) $$ [])

public export
varApp : (n : String) -> {auto prf : In n ns} -> Name -> Term Syntax ns -> Tm ns
varApp n {prf = prf} a v = SynApps (SynVar (Index (idx @{prf})) $$ ((::) {a = a} v []))

-- Finally we define the primitives:
data Primitive where
  PrimTYPE : Primitive PrimNorm []
  PrimBYTES : Primitive PrimNorm []
  PrimBytes : Primitive PrimNorm []
  PrimEmbedBYTES : Primitive PrimNorm [(Explicit, "staticBytes")]
  PrimUnsized : Primitive PrimNorm [(Explicit, "bytes")]

-- Shorthands for some primitives
-- Sad that Idris doesn't have pattern synonyms

public export
TYPE : Term d ns
TYPE = PrimNormal (PrimTYPE $$ [])

public export
BYTES : Term d ns
BYTES = PrimNormal (PrimBYTES $$ [])

public export
Bytes : Term d ns
Bytes = PrimNormal (PrimBytes $$ [])

public export
Unsized : Term d ns -> Term d ns
Unsized b = PrimNormal (PrimUnsized $$ [b])

public export
EmbedBYTES : Term d ns -> Term d ns
EmbedBYTES b = PrimNormal (PrimEmbedBYTES $$ [b])

public export
Sized : Term d ns -> Term d ns
Sized b = Unsized (EmbedBYTES b)
