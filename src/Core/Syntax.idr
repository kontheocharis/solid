-- Defining the syntax of the core language
module Core.Syntax

import Utils
import Core.Base
import Decidable.Equality

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

public export
DecEq Stage where
  decEq Obj Obj = Yes Refl
  decEq Mta Mta = Yes Refl
  decEq Obj Mta = No (\Refl impossible)
  decEq Mta Obj = No (\Refl impossible)

-- Whether an expression head is reducible
public export
data Reducibility : Type where
  -- Reducible because it is callable with an argument.
  Callable : Reducibility

  -- Reducible because it is a lazy value, it can be forced (i.e. a thunk).
  Thunk : Reducibility
  -- Irreducible, i.e. rigid.
  Rigid : Reducibility

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

-- Whether a primitive is reducible or not.
--
-- If it is redicuble, it might have some computation rules depending on its arguments.
public export
data PrimitiveReducibility = PrimReducible | PrimIrreducible

-- The theory of primitives.
--
-- Consists of a list of operators, each of a specified arity. Equations are
-- given separately later (they are the reduction rules). Will also be given
-- proper types later.
public export
data Primitive : PrimitiveClass -> PrimitiveReducibility -> Arity -> Type

export infixr 5 $$

-- The list of binders in the language, indexed by stage.
--
-- Each of these might carry some data.
public export
data Binder : Stage -> Reducibility -> Domain -> Ctx -> Type where
  -- Meta or object-level lambda
  BindLam : Binder s Callable d ns

  -- Meta or object-level let
  BindLet : (ty : Term d ns) -> (rhs : Term d ns) -> Binder s Thunk d ns

  -- Meta or object-level pi
  BindPi : (dom : Term d ns) -> Binder s Rigid d ns

-- Binder is a functor
public export
mapBinder : (Term d ns -> Term d' ms) -> Binder md r d ns -> Binder md r d' ms
mapBinder _ BindLam = BindLam
mapBinder f (BindLet ty t) = BindLet (f ty) (f t)
mapBinder f (BindPi t) = BindPi (f t)

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
data Body : Domain -> Ident -> Ctx -> Type where
  Delayed : Term Syntax (ns :< n) -> Body Syntax n ns
  Closure : Sub ns (Term Value) ms -> Term Syntax (ms :< n) -> Body Value n ns

-- Helper to package a binder with its body.
public export
data Binding : Stage -> Reducibility -> Domain -> Ctx -> Type where
  Bound : (md : Stage) -> (n : Ident) -> Binder md r d ns -> Body d n ns -> Binding md r d ns

-- Different spine heads, meaning x in `x a1 ... an`, are reduced
-- to different extents.
--
-- Unification might have to look at simplified heads, but code extraction only
-- needs normalised heads. I.e. we never reduce object bindings unless we have to.
public export
data HeadKind : Domain -> Type where
  -- Anything goes in syntax
  NA : HeadKind Syntax
  -- A merely normalised head. This might be unforced.
  Normalised : HeadKind Value
  -- A fully simplified head, fully forced.
  Simplified : HeadKind Value

-- This is a fully applied primitive.
public export
data PrimitiveApplied : PrimitiveClass -> (d : Domain) -> HeadKind d -> Ctx -> Type where
  -- Syntactic primitive
  ($$) : {k : PrimitiveClass} -> {r : PrimitiveReducibility}
    -> Primitive k r ar
    -> Spine ar (Term Syntax) ns
    -> PrimitiveApplied k Syntax NA ns
  -- Fully simplified primitive value
  SimpApplied : {k : PrimitiveClass} -> {r : PrimitiveReducibility}
    -> Primitive k r ar
    -> Spine ar (Term Value) ns
    -> PrimitiveApplied k Value Simplified ns
  -- Glued normalised primitive value, which can (definitely) be evaluated further, stored in a lazy value.
  GluedApplied : {k : PrimitiveClass} -> Primitive k PrimReducible ar
    -> Spine ar (Term Value) ns
    -> Lazy (Term Value ns)
    -> PrimitiveApplied k Value Normalised ns

public export
data Head : (d : Domain) -> HeadKind d -> Ctx -> Type where
  -- Variables and metas are simplified if they are values
  SynVar : Variable Syntax ns -> Head Syntax NA ns
  ValVar : Variable Value ns -> Head Value Simplified ns
  SynMeta : MetaVar -> Head Syntax NA ns
  ValMeta : MetaVar -> Head Value Simplified ns

  -- A syntactic binding
  SynBinding : (s : Stage) -> (r : Reducibility) -> Binding s r Syntax ns -> Head Syntax NA ns

  -- Meta-level callable bindings cannot appear as heads in values.
  --
  -- Thus, all we have are object-level bindings (which are merely normalised because
  -- they can technically be more simplified)
  ObjCallable : Binding Obj Callable Value ns -> Head Value Normalised ns
  ObjLazy : Binding Obj Thunk Value ns -> Head Value Normalised ns

  -- An applied primitive can only be a head if it is neutral.
  PrimNeutral : PrimitiveApplied PrimNeu d e ns -> Head d e ns

-- Head applied to a spine.
namespace HeadApplied
  public export
  data HeadApplied : (d : Domain) -> HeadKind d -> Ctx -> Type where
    ($$) : Head d hk ns -> Spine ar (Term d) ns -> HeadApplied d hk ns

-- A lazy value could be evaluated further.
public export
data LazyValue : Ctx -> Type where
  -- A lazy application with a merely normalised (but not fully simplified) head.
  LazyApps : HeadApplied Value Normalised ns -> Lazy (Term Value ns) -> LazyValue ns
  -- A lazy primitive which might reduce further if its arguments do.
  LazyPrimNormal : PrimitiveApplied PrimNorm Value Normalised ns -> LazyValue ns

-- Extract the fully simplified form of a lazy value.
public export
simplified : LazyValue ns -> Lazy (Term Value ns)
simplified (LazyApps h f) = f
simplified (LazyPrimNormal (GluedApplied _ _ f)) = f

public export
data Term where
  -- Spine applied to syntactic head
  SynApps : HeadApplied Syntax NA ns -> Term Syntax ns

  -- A lazy glued value, which could be evaluated further.
  Glued : LazyValue ns -> Term Value ns

  -- Spine applied to a simplified value head
  --
  -- Cannot be reduced further
  SimpApps : HeadApplied Value Simplified ns -> Term Value ns

  -- Callable meta binding, never applied to a spine
  MtaCallable : Binding Mta Callable Value ns -> Term Value ns

  -- Callable object binding that must be simplified if applied to anything.
  --
  -- If it shouldn't be simplified it should be a GluedApps (ObjCallable ..) instead.
  SimpObjCallable : Binding Obj Callable Value ns -> Term Value ns

  -- Rigid binding, never applied (e.g. Pi).
  RigidBinding : (md : Stage) -> Binding md Rigid d ns -> Term d ns

  -- Normal primitives, never applied.
  SynPrimNormal : PrimitiveApplied PrimNorm Syntax NA ns -> Term Syntax ns
  -- Fully simplified primitives, cannot be reduced further, stable under OPEs.
  SimpPrimNormal : PrimitiveApplied PrimNorm Value Simplified ns -> Term Value ns

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
varApp : (n : String) -> {auto prf : In n ns} -> Ident -> Term Syntax ns -> Tm ns
varApp n {prf = prf} a v = SynApps (SynVar (Index (idx @{prf})) $$ ((::) {a = a} v []))

-- Finally we define the primitives:
data Primitive where
  PrimTYPE : Primitive PrimNorm PrimIrreducible []
  PrimBYTES : Primitive PrimNorm PrimIrreducible []
  PrimZeroBYTES : Primitive PrimNorm PrimIrreducible []
  PrimSizeBYTES : Primitive PrimNorm PrimIrreducible []
  PrimPtrBYTES : Primitive PrimNorm PrimIrreducible []
  PrimBytes : Primitive PrimNorm PrimIrreducible []
  PrimEmbedBYTES : Primitive PrimNorm PrimIrreducible [(Explicit, "staticBytes")]
  PrimUnsized : Primitive PrimNorm PrimIrreducible [(Explicit, "bytes")]
  PrimAddBYTES : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]
  PrimAddBytes : Primitive PrimNorm PrimReducible [(Explicit, "a"), (Explicit, "b")]

-- Can't be DecEq without writing out all cases smh
public export
primEq : (a : Primitive k r ar) -> (b : Primitive k' r' ar') -> Maybe (a = b)
primEq PrimTYPE PrimTYPE = Just Refl
primEq PrimBYTES PrimBYTES = Just Refl
primEq PrimZeroBYTES PrimZeroBYTES = Just Refl
primEq PrimSizeBYTES PrimSizeBYTES = Just Refl
primEq PrimPtrBYTES PrimPtrBYTES = Just Refl
primEq PrimBytes PrimBytes = Just Refl
primEq PrimEmbedBYTES PrimEmbedBYTES = Just Refl
primEq PrimUnsized PrimUnsized = Just Refl
primEq PrimAddBYTES PrimAddBYTES = Just Refl
primEq PrimAddBytes PrimAddBytes = Just Refl
primEq _ _ = Nothing
