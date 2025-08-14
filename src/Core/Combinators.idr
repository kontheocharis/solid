module Core.Combinators

import Data.DPair
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Metavariables
import Core.Unification
import Core.Primitives.Rules
import Core.Atoms

-- Annotation versions of syntax

public export covering
($>) : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility}
    -> Primitive k r na ar
    -> Spine ar Atom ns
    -> Atom ns
($>) p sp = Choice (sPrim p sp.syn) (vPrim p sp.val)

public export covering
mtaA : Size ns => Annot ns
mtaA = MkAnnot (PrimTYPE $> []) (PrimTYPE $> []) Mta

public export covering
mta : Size ns => Atom ns -> Expr ns
mta x = MkExpr x mtaA

public export covering
objDynA : Size ns => Atom ns -> Annot ns
objDynA bx = MkAnnot
  (PrimTypeDyn $> [(Val _, bx)])
  (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, PrimZeroLayout $> [])])])
  Obj

public export covering
objDyn : Size ns => Atom ns -> Atom ns -> Expr ns
objDyn bx x = MkExpr x (objDynA bx)

public export covering
objA : Size ns => Atom ns -> Annot ns
objA bx = objDynA (PrimSta $> [(Val _, bx)])

public export covering
obj : Size ns => Atom ns -> Atom ns -> Expr ns
obj bx x = objDyn (PrimSta $> [(Val _, bx)]) x

public export covering
objZA : Size ns => Annot ns
objZA = objA (PrimZeroLayout $> [])

public export covering
objZ : Size ns => Atom ns -> Expr ns
objZ x = obj (PrimZeroLayout $> []) x

public export covering
layoutA : Size ns => Annot ns
layoutA = (mta (PrimLayout $> [])).a

public export covering
layoutDynA : Size ns => Annot ns
layoutDynA = (mta (PrimLayoutDyn $> [])).a

public export covering
objZOrMta : Size ns => Stage -> Atom ns -> Expr ns
objZOrMta Obj a = objZ a
objZOrMta Mta a = mta a

public export
unitTy : Size ns => (s : Stage) -> ExprAt s ns
unitTy = ?unitTyImpl

-- public export
-- irrTy : Size ns => Atom ns -> AtomTy ns -> ExprAt Obj ns
-- irrTy = ?irrTyImpl
  
public export
ioTy : Size ns => ExprAt Obj ns -> ExprAt Obj ns
ioTy = ?ioTyImpl

-- public export covering
-- app : Size ns => Atom ns -> Ident -> Atom ns -> Atom ns
-- app f a x = promote $ apps f.val [(Val a, x.val)]

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
(.a) : Size ns => SortData s k ns -> AnnotAt s ns
(.a) MtaSort = mtaA.f
(.a) (ObjSort Dyn by) = (objDynA by).f
(.a) (ObjSort Sized by) = (objA by).f

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
  (.asAnnot) (MkAnnotFor d i) = MkAnnotAt i d.a.ty

  -- The sort information for the annotation.
  public export
  (.sortData) : AnnotFor s k annotTy ns -> SortData s k ns
  (.sortData) (MkAnnotFor d _) = d

  -- Open an annotation containing a body
  public export covering
  (.open) : Size ns => AnnotFor s k (AtomBody n) ns -> AnnotFor s k Atom (ns :< n')
  (.open) (MkAnnotFor d i) = MkAnnotFor (wkS d) i.open
  
-- Language items

-- Create a glued application expression.
public export covering
glued : {d : Domain} -> Size ns => Variable d (ns :< n) -> Atom (ns :< n) -> Atom (ns :< n)
glued v t = Choice (here) (Glued (LazyApps (ValDef (Level here) $$ []) t.val))

-- Create a metavariable expression.
public export covering
meta : Size ns => MetaVar -> Spine ar Atom ns -> AnnotAt s ns -> ExprAt s ns
meta m sp annot = MkExprAt (promote $ SimpApps (ValMeta m $$ map (force . (.val)) sp)) annot
      
-- Create a lambda expression
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
        (mta (promote $ vMtaPi piIdent bindTy.val bodyClosure.val)).a.f
    Obj => do
      let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot
      let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot
      MkExprAt
        (promote $ sObjLam lamIdent ba.syn bb.syn body.open.syn)
        (obj (promote ptrLayout) (promote $ vObjPi piIdent ba.val bb.val bindTy.val bodyClosure.val)).a.f
          
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
    (mta (promote $ sMtaPi piIdent bindTy.syn bodyClosure.open.syn)).f
  Obj =>
    let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot in
    let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot in
    (obj (promote ptrLayout) (promote $ sObjPi piIdent ba.syn bb.syn bindTy.syn bodyClosure.open.syn)).f
    
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

-- Shorthand for meta-level pis.
public export covering
mtaPi : Size ns => (n : Ident) -> AtomTy ns -> AtomTy (ns :< n) -> Atom ns
mtaPi piIdent bindTy bodyTy = (pi Mta piIdent (MkAnnotFor MtaSort bindTy) (MkAnnotFor MtaSort (close idS bodyTy))).tm
          
-- Create a variable expression with the given index and annotation.
public export covering
var : Size ns => Idx ns -> AnnotAt s ns -> ExprAt s ns
var idx annot = MkExprAt (promote (varIdx idx)) annot

public export covering
apps : Size ns => Expr ns -> Spine ar Expr ns -> Expr ns

-- Find a variable by its name in the context.
public export covering
v : Size ns => (n : String) -> {auto prf : In n ns} -> Atom ns
v n = promote (var n)

public export covering
mtaSigma : Size ns => (n : Ident) -> AtomTy ns -> Atom ns -> Atom ns
mtaSigma piIdent bindTy bodyTy = ?ajajajaj

public export covering
gatherPi : Size ns => Annot ns -> (ar : Arity) -> Maybe (Tel ar Annot ns, Annot (ns ::< ar))