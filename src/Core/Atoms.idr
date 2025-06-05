-- A representation of terms which lazily stores both syntax and values.
module Core.Atoms

import Data.DPair
import Common
import Decidable.Equality
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

namespace ValSpine
  public export
  (.val) : Spine ar (AnyDomain tm) ns -> Spine ar (tm Value) ns
  (.val) sp = mapSpine (force . (.val)) sp

  public export
  (.syn) : Spine ar (AnyDomain tm) ns -> Spine ar (tm Syntax) ns
  (.syn) sp = mapSpine (force . (.syn)) sp
  
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
  -> Lazy (tm d ns)
  -> AnyDomain tm ns
promote {d = Syntax} tm = Choice tm (eval id tm) 
promote {d = Value} val = Choice (quote val) val

public export
(WeakSized (tm Syntax), Weak (tm Value)) => WeakSized (AnyDomain tm) where
  weakS e (Choice syn val) = Choice (weakS e syn) (weak e val)

public export covering
(WeakSized (tm Syntax), Vars (tm Value), Psh tm) => Vars (AnyDomain tm) where
  here = promote {tm = tm} here

public export
(EvalSized (over Value) (tm Syntax) (tm Value), Quote (tm Value) (tm Syntax))
  => EvalSized (AnyDomain over) (AnyDomain tm) (AnyDomain tm) where
  evalS env (Choice syn val) = let ev = delay (evalS (mapSub (force . (.val)) env) syn) in Choice (quote ev) ev

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
  close : Sub ns Atom ns -> Atom (ns :< n) -> AtomBody n ns
  close env t = Choice (Delayed t.syn) (Closure (mapSub (force . (.val)) env) t.syn)

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
  
namespace ExprAt
  public export
  asTypeIn : Atom ns -> AnnotAt s ns -> AnnotAt s ns
  asTypeIn ty (MkAnnotAt sort _) = MkAnnotAt ty sort
  
  public export
  (.toAnnot) : ExprAt s ns -> AnnotAt s ns
  (.toAnnot) (MkExprAt ty (MkAnnotAt sort s)) = MkAnnotAt ty sort


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
WeakSized Annot where
  weakS e (MkAnnot t a s) = MkAnnot (weakS e t) (weakS e a) s

public export covering
EvalSized Atom Annot Annot where
  evalS env (MkAnnot ty sort s) = MkAnnot (evalS env ty) (evalS env sort) s

public export covering
WeakSized (AnnotAt s) where
  weakS e (MkAnnotAt t a) = MkAnnotAt (weakS e t) (weakS e a)

public export covering
EvalSized Atom (AnnotAt s) (AnnotAt s) where
  evalS env (MkAnnotAt ty sort) = MkAnnotAt (evalS env ty) (evalS env sort)

public export covering
WeakSized Expr where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalSized Atom Expr Expr where
  evalS env (MkExpr tm a) = MkExpr (evalS env tm) (evalS env a)

public export covering
WeakSized (ExprAt s) where
  weakS e (MkExprAt t a) = MkExprAt (weakS e t) (weakS e a)

public export covering
EvalSized Atom (ExprAt s) (ExprAt s) where
  evalS env (MkExprAt tm a) = MkExprAt (evalS env tm) (evalS env a)

-- Annotation versions of syntax
  
-- The type of types, for the given stage.
-- 
-- For the meta level, this is TYPE
-- For the object level, this is Type 0.
public export covering
typeOfTypeAnnot : Size ns => (s : Stage) -> AnnotAt s ns
typeOfTypeAnnot stage = let t = promote $ typeOfTypesForStage stage in MkAnnotAt t t

-- TYPE as an annotation
public export covering
mtaTypeAnnot : Size ns => AnnotAt Mta ns
mtaTypeAnnot = let t = promote {tm = Term} mtaType in MkAnnotAt t t

-- Dyn b as an annotation
public export covering
dynObjTypeAnnot : Size ns => Atom ns -> AnnotAt Obj ns
dynObjTypeAnnot b = MkAnnotAt --@@Todo: more performant
  (promote $ dynObjType b.syn)
  (promote $ sizedObjType zeroBytes)

-- Type b as an annotation
public export covering
sizedObjTypeAnnot : Size ns => Atom ns -> AnnotAt Obj ns
sizedObjTypeAnnot b = MkAnnotAt --@@Todo: more performant
  (promote $ sizedObjType b.syn)
  (promote $ sizedObjType zeroBytes)

-- Partially static bytes, the argument to Dyn
public export covering
psBytesAnnot : Size ns => AnnotAt Mta ns
psBytesAnnot = MkAnnotAt (promote psBytes) (promote mtaType)

-- Static bytes, the argument to Type
public export covering
staBytesAnnot : Size ns => AnnotAt Mta ns
staBytesAnnot = MkAnnotAt (promote staBytes) (promote mtaType)

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
(.asAnnot) MtaSort = mtaTypeAnnot
(.asAnnot) (ObjSort Dyn by) = dynObjTypeAnnot by
(.asAnnot) (ObjSort Sized by) = sizedObjTypeAnnot by

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
  
-- Language items
  
public export
primAnnot : (p : Primitive k r ar) -> (Tel ar Annot ns, Annot (ns ::< ar))
primAnnot = ?primAnnotImpl

public export covering
glued : {d : Domain} -> Size ns => Variable d (ns :< n) -> Atom (ns :< n) -> Atom (ns :< n)
glued v t = Choice (here) (Glued (LazyApps (ValDef (Level here) $$ []) t.val))

-- Make a metavariable expression with the given data.
public export covering
meta : Size ns => MetaVar -> Spine ar Atom ns -> AnnotAt s ns -> ExprAt s ns
meta m sp annot = MkExprAt (promote $ SimpApps (ValMeta m $$ mapSpine (force . (.val)) sp)) annot
      
-- Create a lambda expression with the given data.
public export covering
lam : Size ns
  => (piStage : Stage)
  -> (piIdent : Ident)
  -> (lamIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (AtomBody piIdent) ns)
  -> (body : AtomBody lamIdent ns)
  -> ExprAt piStage ns
lam piStage piIdent lamIdent bindAnnot bodyAnnot body =
  case piStage of
    Mta => do
      let MkAnnotFor MtaSort bindTy = bindAnnot
      let MkAnnotFor MtaSort bodyClosure = bodyAnnot
      MkExprAt
        (promote $ sMtaLam lamIdent body.open.syn)
        ((promote $ vMtaPi piIdent bindTy.val bodyClosure.val)
          `asTypeIn` mtaTypeAnnot)
    Obj => do
      let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot
      let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot
      MkExprAt
        (promote $ sObjLam lamIdent ba.syn bb.syn body.open.syn)
        ((promote $ vObjPi piIdent ba.val bb.val bindTy.val bodyClosure.val)
          `asTypeIn` sizedObjTypeAnnot (Choice ptrBytes ptrBytes))
          
-- Create a pi expression
public export covering
pi : Size ns
  => (piStage : Stage)
  -> (piIdent : Ident)
  -> (bindAnnot : AnnotFor piStage Sized AtomTy ns)
  -> (bodyAnnot : AnnotFor piStage Sized (AtomBody piIdent) ns)
  -> ExprAt piStage ns
pi piStage piIdent bindAnnot bodyAnnot = case piStage of
  Mta =>
    let MkAnnotFor MtaSort bindTy = bindAnnot in
    let MkAnnotFor MtaSort bodyClosure = bodyAnnot in
    MkExprAt (promote $ sMtaPi piIdent bindTy.syn bodyClosure.open.syn) (mtaTypeAnnot)
  Obj =>
    let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot in
    let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot in
    MkExprAt
      (promote $ sObjPi piIdent ba.syn bb.syn bindTy.syn bodyClosure.open.syn)
      (sizedObjTypeAnnot (Choice ptrBytes ptrBytes)) -- @@Todo: clean this Choice up

-- The type of the callback that `ifForcePi` calls when it finds a matching
-- type.
public export
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
public export covering
ifForcePi : Size ns
  => (stage : Stage)
  -> (ident : Ident)
  -> (potentialPi : AtomTy ns)
  -> (ifMatching : ForcePiCallback r stage ns)
  -> (ifMismatching : (stage' : Stage) -> ForcePiCallback r stage' ns)
  -> (otherwise : AtomTy ns -> r)
  -> r
ifForcePi stage (mode, name) potentialPi ifMatching ifMismatching otherwise
  = case potentialPi.val of
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
    -- fail
    resolvedPi => otherwise (promote resolvedPi)
          
-- Create a variable expression with the given index and annotation.
public export covering
var : Size ns => Idx ns -> AnnotAt s ns -> ExprAt s ns
var idx annot = MkExprAt (promote (varIdx idx)) annot

-- Create a primitive expression with the given data.
public export covering
prim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility} -> Primitive k r ar -> Spine ar Atom ns -> Expr ns
prim @{s} p sp =
  let (_, pRet) = primAnnot {ns = ns} p in
  let ret = sub {sms = s + sp.count} (idS ::< sp) pRet.ty in
  let retSort = sub {sms = s + sp.count} (idS ::< sp) pRet.sort in
  MkExpr (Choice (sPrim p sp.syn) (vPrim p sp.val)) (MkAnnot ret retSort pRet.stage)