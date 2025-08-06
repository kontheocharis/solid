-- A representation of terms which lazily stores both syntax and values.
module Core.Atoms

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
  (.val) sp = map (force . (.val)) sp

  public export
  (.syn) : Spine ar (AnyDomain tm) ns -> Spine ar (tm Syntax) ns
  (.syn) sp = map (force . (.syn)) sp
  
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
  
public export
(Relabel (tm Value), Relabel (tm Syntax)) => Relabel (AnyDomain tm) where
  relabel r (Choice syn val) = Choice (relabel r syn) (relabel r val)

-- Atom bodies
namespace AtomBody
  -- The atom version of a closure.
  public export
  AtomBody : Ident -> Ctx -> Type
  AtomBody n = AnyDomain (\d => Body d n)

  -- Turn a body into a term in an extended context.
  public export covering
  (.open) : Size ns => AtomBody n ns -> Atom (ns :< n')
  (.open) (Choice (Delayed s) (Closure env v)) = Choice (relabel (Change _ Id) s) (eval (lift env) v)

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
  -- Turn `AnnotAt` into `Annot`
  public export
  (.p) : {s : Stage} -> AnnotAt s ns -> Annot ns
  (.p) (MkAnnotAt ty sort) = MkAnnot ty sort s

  public export
  (.f) : (e : Annot ns) -> AnnotAt e.stage ns
  (.f) (MkAnnot ty sort s) = MkAnnotAt ty sort

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
  (.p) : {s : Stage} -> ExprAt s ns -> Expr ns
  (.p) (MkExprAt tm a) = MkExpr tm a.p

  public export
  (.f) : (e : Expr ns) -> ExprAt e.annot.stage ns
  (.f) (MkExpr tm a) = MkExprAt tm a.f
  
  public export
  asTypeIn : Atom ns -> Annot ns -> Annot ns
  asTypeIn ty (MkAnnot sort _ s) = MkAnnot ty sort s
  
  public export
  (.a) : Expr ns -> Annot ns
  (.a) (MkExpr ty (MkAnnot sort s st)) = MkAnnot ty sort st
  
  public export
  (.e) : Annot ns -> Atom ns -> Expr ns
  (.e) (MkAnnot ty sort st) s = MkExpr ty (MkAnnot sort s st)
  
namespace ExprAt
  public export
  asTypeIn : Atom ns -> AnnotAt s ns -> AnnotAt s ns
  asTypeIn ty (MkAnnotAt sort _) = MkAnnotAt ty sort
  
  public export
  (.a) : ExprAt s ns -> AnnotAt s ns
  (.a) (MkExprAt ty (MkAnnotAt sort s)) = MkAnnotAt ty sort


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

-- Operations
public export
Op : Arity -> Ctx -> Type
Op ar ns = (Tel ar Annot ns, Annot (ns ::< ar))
  
public export covering
Relabel Annot where
  relabel r (MkAnnot ty sort s) = MkAnnot (relabel r ty) (relabel r sort) s

public export covering
WeakSized Annot where
  weakS e (MkAnnot t a s) = MkAnnot (weakS e t) (weakS e a) s

public export covering
EvalSized Atom Annot Annot where
  evalS env (MkAnnot ty sort s) = MkAnnot (evalS env ty) (evalS env sort) s

public export covering
Relabel (AnnotAt s) where
  relabel r (MkAnnotAt ty sort) = MkAnnotAt (relabel r ty) (relabel r sort)

public export covering
WeakSized (AnnotAt s) where
  weakS e (MkAnnotAt t a) = MkAnnotAt (weakS e t) (weakS e a)

public export covering
EvalSized Atom (AnnotAt s) (AnnotAt s) where
  evalS env (MkAnnotAt ty sort) = MkAnnotAt (evalS env ty) (evalS env sort)

public export covering
Relabel Expr where
  relabel r (MkExpr t a) = MkExpr (relabel r t) (relabel r a)

public export covering
WeakSized Expr where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalSized Atom Expr Expr where
  evalS env (MkExpr tm a) = MkExpr (evalS env tm) (evalS env a)

public export covering
Relabel (ExprAt s) where
  relabel r (MkExprAt t a) = MkExprAt (relabel r t) (relabel r a)

public export covering
WeakSized (ExprAt s) where
  weakS e (MkExprAt t a) = MkExprAt (weakS e t) (weakS e a)

public export covering
EvalSized Atom (ExprAt s) (ExprAt s) where
  evalS env (MkExprAt tm a) = MkExprAt (evalS env tm) (evalS env a)

public export covering
Relabel (Op ar) where
  relabel r (a, b) = (relabel r a, relabel (keepMany r) b)
  
export covering
Show (Term Syntax ns) => Show (Atom ns) where
  show a = show a.syn