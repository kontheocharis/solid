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
-- All these should only be called on *well-typed terms!*

public export covering
resolve : HasMetas m => Size ns => Atom ns -> m sm (Atom ns)
resolve x = do
  t <- resolveGlueAndMetas {sm = sm} x.val
  pure $ promote t

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

public export covering
objZOrMtaA : Size ns => (s : Stage) -> AnnotAt s ns
objZOrMtaA Obj = objZA.f
objZOrMtaA Mta = mtaA.f

-- Sorts

-- A sort can be either static (meta-level), dynamic (object-level with a
-- runtime size), or sized (object-level with a compile-time size).
public export
data SortKind : Stage -> Type where
  Static : SortKind Mta
  Dyn : SortKind s
  Sized : SortKind s
  
public export
loosestSortKind : (s : Stage) -> SortKind s
loosestSortKind Mta = Static
loosestSortKind Obj = Dyn
  
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
sortBytes : Size ns => SortData Obj s ns -> Atom ns
sortBytes (ObjSort Dyn by) = by
sortBytes (ObjSort Sized by) = PrimSta $> [(Val _, by)]
  
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
    
  public export
  ExprFor : (s : Stage) -> SortKind s -> (ns : Ctx) -> Type
  ExprFor s k = ExprShape (AnnotFor s k Atom)
    
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

  -- Apply a body annotation to an argument
  public export covering
  apply : Size ns => AnnotFor s k (AtomBody n) ns -> Atom ns -> AnnotFor s k Atom ns
  apply (MkAnnotFor d i) arg = MkAnnotFor d (apply i arg)
  
-- Language items

-- Create a glued application expression.
public export covering
glued : {d : Domain} -> Size ns => Variable d (ns :< n) -> Atom (ns :< n) -> Atom (ns :< n)
glued v t = Choice (here) (Glued (LazyApps (ValDef (Level here) $$ []) t.val))

-- Create a metavariable atom.
public export covering
aMeta : Size ns => MetaVar -> Spine ar Atom ns -> Atom ns
aMeta m sp = promote $ SimpApps (ValMeta m $$ map (force . (.val)) sp)

-- Create a metavariable expression.
public export covering
meta : Size ns => MetaVar -> Spine ar Atom ns -> AnnotAt s ns -> ExprAt s ns
meta m sp annot = MkExpr (aMeta m sp) annot

-- Create a fresh metavariable
public export covering
newMeta : HasMetas m => Size ns => Maybe Name -> m sm (Atom ns)
newMeta {ns = ns} n = do -- @@Todo: use type
  m <- newMeta n
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure $ aMeta m ?ins
      
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
      MkExpr
        (promote $ sMtaLam lamIdent body.open.syn)
        (mta (promote $ vMtaPi piIdent bindTy.val bodyClosure.val)).a.f
    Obj => do
      let MkAnnotFor (ObjSort Sized ba) bindTy = bindAnnot
      let MkAnnotFor (ObjSort Sized bb) bodyClosure = bodyAnnot
      MkExpr
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
    
public export
record PiData (stage : Stage) (ns : Ctx) where
  constructor MkPiData
  resolvedPi : AtomTy ns
  piIdent : Ident
  a : AnnotFor stage Sized Atom ns
  b : AnnotFor stage Sized (AtomBody piIdent) ns

public export
data ForcePi : Ctx -> Type where
  -- Matching pi
  MatchingPi : (stage : Stage) -> PiData stage ns -> ForcePi ns
  -- Not a pi
  OtherwiseNotPi : AtomTy ns -> ForcePi ns

public export
data ForcePiAt : Stage -> Ctx -> Type where
  -- Matching pi
  MatchingPiAt : PiData s ns -> ForcePiAt s ns
  -- Mismatching pi with the given stage
  MismatchingPiAt : (stage' : Stage) -> PiData stage' ns -> ForcePiAt s ns
  -- Not a pi
  OtherwiseNotPiAt : AtomTy ns -> ForcePiAt s ns

-- Given a `potentialPi`, try to force it to be a pi type
public export covering
forcePi : HasMetas m => Size ns => (potentialPi : AtomTy ns) -> m sm (ForcePi ns)
forcePi potentialPi
  = resolve potentialPi >>= \a => case a.val of
    resolvedPi@(RigidBinding piStage@Obj (Bound _ (BindObjPi (piMode, piName) ba bb a) b)) => 
      let
        ba' = promote ba
        bb' = promote bb
        piData = MkPiData (promote resolvedPi) (piMode, piName)
          (MkAnnotFor (ObjSort Sized ba') (promote a))
          (MkAnnotFor (ObjSort Sized bb') (promoteBody b))
      in pure $ MatchingPi Obj piData
    resolvedPi@(RigidBinding piStage@Mta (Bound _ (BindMtaPi (piMode, piName) a) b)) =>
      let
        piData = MkPiData (promote resolvedPi) (piMode, piName)
          (MkAnnotFor MtaSort (promote a))
          (MkAnnotFor MtaSort (promoteBody b))
      in pure $ MatchingPi Mta piData
    v => pure $ OtherwiseNotPi (newVal v potentialPi)

-- Given a `potentialPi`, try to match it given that we expect something in
-- `mode` and `stage`.
public export covering
forcePiAt : HasMetas m => Size ns
  => (stage : Stage)
  -> (ident : Ident)
  -> (potentialPi : AtomTy ns)
  -> m sm (ForcePiAt stage ns)
forcePiAt stage (mode, name) potentialPi = forcePi potentialPi >>= \case
  MatchingPi piStage piData@(MkPiData resolvedPi (piMode, piName) a b) =>
    pure $ case decEq (piMode, piStage) (mode, stage) of
      Yes Refl => MatchingPiAt piData
      _ => MismatchingPiAt piStage piData
  OtherwiseNotPi tm => pure $ OtherwiseNotPiAt tm
  
public export
data ForceLam : Ctx -> Type where
  MatchingLam : (stage : Stage) -> AtomBinder stage Callable n ns -> AtomBody n ns -> ForceLam ns
  OtherwiseNotLam : Atom ns -> ForceLam ns

-- Given a `potentialLam`, try to force it to be a lambda
public export covering
forceLam : HasMetas m => Size ns => (potentialLam : Atom ns) -> m sm (ForceLam ns)
forceLam potentialLam = resolve potentialLam >>= \a => case a.val of
  MtaCallable (Bound Mta binder body) => pure $ MatchingLam Mta (promoteBinder binder) (promoteBody body)
  SimpObjCallable (Bound Obj binder body) => pure $ MatchingLam Obj (promoteBinder binder) (promoteBody body)
  -- @@Consider: Do we need to handle the glued stuff?
  v => pure $ OtherwiseNotLam (newVal v potentialLam)

-- Shorthand for meta-level pis.
public export covering
mtaPi : Size ns => (n : Ident) -> AtomTy ns -> AtomTy (ns :< n) -> Atom ns
mtaPi piIdent bindTy bodyTy = (pi Mta piIdent (MkAnnotFor MtaSort bindTy) (MkAnnotFor MtaSort (close idS bodyTy))).tm
          
-- Create a variable expression with the given index and annotation.
public export covering
var : Size ns => Idx ns -> AnnotAt s ns -> ExprAt s ns
var idx annot = MkExpr (promote (varIdx idx)) annot

public export covering
apps : Size ns => Expr ns -> Spine ar Expr ns -> AnnotAt s ns -> ExprAt s ns
apps f xs a = MkExpr (promote $ sApps f.tm.syn (map (.tm.syn) xs)) a

-- Find a variable by its name in the context.
public export covering
v : Size ns => (n : String) -> {auto prf : In n ns} -> Atom ns
v n = promote (var n)

public export
data GatherPis : Arity -> Ctx -> Type where
  Gathered : Tel ar Annot ns -> Annot (ns ::< ar) -> GatherPis ar ns
  TooMany : (extra : Count ar) -> (under : Count ar') -> AtomTy (ns ::< ar') -> GatherPis ar ns

public export covering
gatherPis : HasMetas m => Size ns => Annot ns -> (ar : Arity) -> m sm (GatherPis ar ns)
gatherPis x [] = pure $ Gathered [] x
gatherPis x ar@(n :: ns) = forcePi x.ty >>= \case
  MatchingPi _ (MkPiData resolvedPi piIdent a b) => gatherPis b.open.asAnnot.p ns >>= \case
    Gathered params ret => pure $ Gathered ((Val _, a.asAnnot.p) :: params) ret
    TooMany c u t => pure $ TooMany (CS ns.count) (CS u) t
  OtherwiseNotPi t => pure $ TooMany (CS ns.count) CZ t