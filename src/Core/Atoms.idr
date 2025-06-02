-- A representation of terms which lazily stores both syntax and values.
module Core.Atoms

import Data.DPair
import Common
import Core.Base
import Core.Primitives
import Core.Syntax
import Core.Evaluation
import Core.Metavariables
import Core.Unification
import Core.Rules

public export
record AnyDomain (tm : Domain -> Ctx -> Type) (ns : Ctx) where
  constructor Choice
  syn : Lazy (tm Syntax ns)
  val : Lazy (tm Value ns)
  
-- An atom is a term and a value at the same time.
public export
Atom : Ctx -> Type
Atom = AnyDomain Term

public export
AtomTy : Ctx -> Type
AtomTy = AnyDomain Term
  
-- All syntactic presheaf related bounds
public export
0 Psh : (Domain -> Ctx -> Type) -> Type
Psh tm
  = (Eval (Term Value) (tm Syntax) (tm Value),
    Quote (tm Value) (tm Syntax),
    Weak (tm Value))
  
-- Promote a term or value to an `AnyDomain` type.
public export covering
promote : Psh tm
  => Size ns
  => {d : Domain}
  -> tm d ns
  -> AnyDomain tm ns
promote {d = Syntax} tm = Choice tm (eval id tm) 
promote {d = Value} val = Choice (quote val) val

public export
(WeakSized (tm Syntax), Weak (tm Value)) => WeakSized (AnyDomain tm) where
  weakS e (Choice syn val) = Choice (weakS e syn) (weak e val)

public export covering
(WeakSized (tm Syntax), Vars (tm Value), Psh tm) => Vars (AnyDomain tm) where
  here = promote {tm = tm} here

-- Substitutions for atoms
public export covering
sub : Psh tm => Size ns => Sub ns Val ms -> AnyDomain tm ms -> AnyDomain tm ns
sub env t = promote {tm = tm} $ eval env t.syn

-- Atom spines
-- @@Reconsider: this is kind of ugly
namespace AtomSpine
  public export
  AtomSpine : Arity -> Ctx -> Type
  AtomSpine ar = AnyDomain (\d => Spine ar (Term d))
  
  public export covering
  Nil : AtomSpine [] ns
  Nil = Choice [] []
  
  public export covering
  (::) : Atom ns -> AtomSpine ar ns -> AtomSpine (n :: ar) ns
  x :: xs = Choice (x.syn :: xs.syn) (x.val :: xs.val)

-- Atom bodies
namespace AtomBody
  -- The atom version of a closure.
  public export
  AtomBody : Ident -> Ctx -> Type
  AtomBody n = AnyDomain (\d => Body d n)

  -- Turn a body into a term in an extended context.
  public export covering
  (.open) : Size ns => AtomBody n ns -> Atom (ns :< n')
  (.open) (Choice (Delayed s) (Closure env v)) = Choice (weakS Relabel s) (eval (lift env) v)

  public export covering
  close : Env ns ns -> Atom (ns :< n) -> AtomBody n ns
  close env t = Choice (Delayed t.syn) (Closure env t.syn)

  -- Promote a syntactical body to an `AtomBody`.
  public export covering
  promoteBody : Size ns
    => {d : Domain}
    -> Body d n ns
    -> AtomBody n ns
  promoteBody b = promote {tm = \d => Body d n} b

-- An annotation is a type and a stage
public export
record Annot (ns : Ctx) where
  constructor MkAnnot
  ty : AtomTy ns
  sort : AtomTy ns
  stage : Stage

-- An annotation at a given stage, which is a type and a sort.
public export
record AnnotAt (s : Stage) (ns : Ctx) where
  constructor MkAnnotAt
  ty : AtomTy ns
  sort : AtomTy ns

namespace Annot
  -- Turn `ExprAt` into `Expr`
  public export
  packStage : {s : Stage} -> AnnotAt s ns -> Annot ns
  packStage (MkAnnotAt ty sort) = MkAnnot ty sort s

  public export
  forgetStage : (e : Annot ns) -> AnnotAt e.stage ns
  forgetStage (MkAnnot ty sort s) = MkAnnotAt ty sort

-- Version of ExprAt which also packages the stage
public export
record Expr (ns : Ctx) where
  constructor MkExpr
  tm : Atom ns
  annot : Annot ns

-- A typed expression at a given stage
public export
record ExprAt (s : Stage) (ns : Ctx) where
  constructor MkExprAt
  tm : Atom ns
  annot : AnnotAt s ns

namespace Expr
  -- Turn `ExprAt` into `Expr`
  public export
  packStage : {s : Stage} -> ExprAt s ns -> Expr ns
  packStage (MkExprAt tm a) = MkExpr tm (packStage a)

  public export
  forgetStage : (e : Expr ns) -> ExprAt e.annot.stage ns
  forgetStage (MkExpr tm a) = MkExprAt tm (forgetStage a)
  
  public export
  asTypeIn : Atom ns -> Annot ns -> Annot ns
  asTypeIn ty (MkAnnot sort _ s) = MkAnnot ty sort s

-- Helper to decide which `Expr` to pick based on an optional stage
public export
0 ExprAtMaybe : Maybe Stage -> Ctx -> Type
ExprAtMaybe Nothing = Expr
ExprAtMaybe (Just s) = ExprAt s

-- Turn `ExprAtMaybe` into `Expr`
public export
maybePackStage : {s : Maybe Stage} -> ExprAtMaybe s ns -> Expr ns
maybePackStage {s = Just s} (MkExprAt tm (MkAnnotAt ty sort)) = MkExpr tm (MkAnnot ty sort s)
maybePackStage {s = Nothing} x = x
  
public export covering
EvalPrims => WeakSized Annot where
  weakS e (MkAnnot t a s) = MkAnnot (weakS e t) (weakS e a) s

public export covering
EvalPrims => WeakSized (AnnotAt s) where
  weakS e (MkAnnotAt t a) = MkAnnotAt (weakS e t) (weakS e a)

public export covering
EvalPrims => WeakSized Expr where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalPrims => WeakSized (ExprAt s) where
  weakS e (MkExprAt t a) = MkExprAt (weakS e t) (weakS e a)

-- Annotation versions of syntax
  
-- The type of types, for the given stage.
-- 
-- For the meta level, this is TYPE
-- For the object level, this is Type 0.
public export covering
typeOfTypeAnnot : Size ns => Stage -> Annot ns
typeOfTypeAnnot stage = let t = promote $ typeOfTypesForStage stage in MkAnnot t t stage

-- TYPE as an annotation
public export covering
mtaTypeAnnot : Size ns => Annot ns
mtaTypeAnnot = let t = promote {tm = Term} mtaType in MkAnnot t t Mta

-- Dyn b as an annotation
public export covering
dynObjTypeAnnot : Size ns => Atom ns -> Annot ns
dynObjTypeAnnot b = MkAnnot --@@Todo: more performant
  (promote $ dynObjType b.syn)
  (promote $ sizedObjType zeroBytes)
  Obj

-- Type b as an annotation
public export covering
sizedObjTypeAnnot : Size ns => Atom ns -> Annot ns
sizedObjTypeAnnot b = MkAnnot --@@Todo: more performant
  (promote $ sizedObjType b.syn)
  (promote $ sizedObjType zeroBytes)
  Obj

-- Partially static bytes, the argument to Dyn
public export covering
psBytesAnnot : Size ns => Annot ns
psBytesAnnot = MkAnnot (promote psBytes) (promote mtaType) Mta

-- Static bytes, the argument to Type
public export covering
staBytesAnnot : Size ns => Annot ns
staBytesAnnot = MkAnnot (promote staBytes) (promote mtaType) Mta

-- Sorts

-- A sort can be either static (meta-level), dynamic (object-level with a
-- runtime size), or sized (object-level with a compile-time size).
public export
data SortKind : Stage -> Type where
  Static : SortKind Mta
  Dyn : SortKind s
  Sized : SortKind s
  
-- The accompanying data for a sort at a given stage.
public export
data SortData : (s : Stage) -> SortKind s -> Ctx -> Type where
  MtaSort : SortData Mta k ns
  -- Object sorts remember their size.
  ObjSort : (k : SortKind Obj) -> (by : Atom ns) -> SortData Obj k ns
  
public export covering
WeakSized (SortData s k) where
  weakS e MtaSort = MtaSort
  weakS e (ObjSort k by) = ObjSort k (weakS e by)
  
-- Convert a `SortData` to its corresponding annotation.
public export covering
(.asAnnot) : Size ns => SortData s k ns -> AnnotAt s ns
(.asAnnot) MtaSort = forgetStage mtaTypeAnnot
(.asAnnot) (ObjSort Dyn by) = forgetStage $ dynObjTypeAnnot by
(.asAnnot) (ObjSort Sized by) = forgetStage $ sizedObjTypeAnnot by

namespace AnnotFor
    
  -- An annotation for a given sort.
  public export
  data AnnotFor : (s : Stage) -> SortKind s -> (annotTy : Ctx -> Type) -> (ns : Ctx) -> Type where
    MkAnnotFor : SortData s k ns -> (inner : annotTy ns) -> AnnotFor s k annotTy ns
    
  -- The actual type of the annotation.
  public export
  (.inner) : AnnotFor s k annotTy ns -> annotTy ns
  (.inner) (MkAnnotFor _ ty) = ty

  -- `AnnotFor` with Atom can be converted to an `AnnotAt` type.
  public export covering
  (.asAnnot) : Size ns => AnnotFor s k Atom ns -> AnnotAt s ns
  (.asAnnot) (MkAnnotFor d i) = MkAnnotAt i d.asAnnot.ty

  -- The sort information for the annotation.
  public export
  (.sortData) : AnnotFor s k annotTy ns -> SortData s k ns
  (.sortData) (MkAnnotFor d _) = d

  -- Open an annotation containing a body
  public export covering
  (.open) : Size ns => AnnotFor s k (AtomBody n) ns -> AnnotFor s k Atom (ns :< n')
  (.open) (MkAnnotFor d i) = MkAnnotFor (wkS d) i.open