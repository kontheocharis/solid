-- A representation of terms which lazily stores both syntax and values.
module Core.Atoms

import Data.DPair
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Utils
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules

public export
record AnyDomain (tm : Domain -> Ctx -> Type) (ns : Ctx) where
  constructor Choice
  syn : Lazy (tm Syntax ns)
  val : Lazy (tm Value ns)
  
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
newSyn : tm Syntax ns -> AnyDomain tm ns -> AnyDomain tm ns
newSyn syn' (Choice syn val) = Choice syn' val

public export
newVal : tm Value ns -> AnyDomain tm ns -> AnyDomain tm ns
newVal val' (Choice syn val) = Choice syn val'
  
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
  
  public export covering
  promoteSpine : Size ns => {d : _} -> Spine ar (Term d) ns -> Spine ar Atom ns
  promoteSpine sp = map (\x => promote x) sp

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
  
public export
(Thin (tm Value), Thin (tm Syntax)) => Thin (AnyDomain tm) where
  thin r (Choice syn val) = Choice (thin r syn) (thin r val)
  
-- Atom binders
namespace AtomBinder
  public export
  0 AtomBinder : Stage -> Reducibility -> Ident -> Ctx -> Type
  AtomBinder s r = BinderShape s r Atom
  
  public export covering
  promoteBinder : Size ns => {d : Domain} -> Binder s r d n ns -> AtomBinder s r n ns
  promoteBinder = mapBinder (\t => promote t)

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
  
  -- Apply a body to an argument
  public export covering
  apply : Size ns => AtomBody n ns -> Atom ns -> Atom ns
  apply (Choice syn (Closure env v)) arg = promote (eval {val = Val} (env :< arg.val) v)

-- An annotation is a type and a stage
public export
record Annot (ns : Ctx) where
  constructor MkAnnot
  ty : AtomTy ns
  sort : AtomTy ns
  stage : Stage

public export
record AnnotShape (typ : Ctx -> Type) (srt : Ctx -> Type) (ns : Ctx) where
  constructor MkAnnotShape
  ty : typ ns
  sort : srt ns
  
-- An annotation at a given stage, which is a type and a sort.
public export
record AnnotAt (s : Stage) (ns : Ctx) where
  constructor MkAnnotAt
  ty : AtomTy ns
  sort : AtomTy ns
  
public export
(.shape) : AnnotAt s ns -> AnnotShape AtomTy AtomTy ns
(MkAnnotAt ty sort) .shape = MkAnnotShape ty sort 

namespace Annot
  -- Turn `AnnotAt` into `Annot`
  public export
  (.p) : {s : Stage} -> AnnotAt s ns -> Annot ns
  (.p) (MkAnnotAt ty sort) = MkAnnot ty sort s

  public export
  (.f) : (e : Annot ns) -> AnnotAt e.stage ns
  (.f) (MkAnnot ty sort s) = MkAnnotAt ty sort

public export
record ExprShape (ann : Ctx -> Type) (ns : Ctx) where
  constructor MkExpr
  tm : Atom ns
  annot : ann ns
  
public export
tmL : Lens (ExprShape ann ns) (Atom ns)
tmL = MkLens (.tm) (\x, u => { tm := x } u)
  
public export
annotL : Lens (ExprShape ann ns) (ann ns)
annotL = MkLens (.annot) (\x, u => { annot := x } u)

public export
mapAnnot : (ann ns -> ann' ns) -> ExprShape ann ns -> ExprShape ann' ns
mapAnnot f (MkExpr tm annot) = MkExpr tm (f annot)

-- Version of ExprAt which also packages the stage
public export
0 Expr : Ctx -> Type
Expr = ExprShape Annot

-- A typed expression at a given stage
public export
0 ExprAt : Stage -> Ctx -> Type
ExprAt s = ExprShape (AnnotAt s)

namespace Expr
  -- Turn `ExprAt` into `Expr`
  public export
  (.p) : {s : Stage} -> ExprAt s ns -> Expr ns
  (.p) (MkExpr tm a) = MkExpr tm a.p

  public export
  (.f) : (e : Expr ns) -> ExprAt e.annot.stage ns
  (.f) (MkExpr tm a) = MkExpr tm a.f
  
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
  (.a) (MkExpr ty (MkAnnotAt sort s)) = MkAnnotAt ty sort
  
  public export
  (.e) : AnnotAt s ns -> Atom ns -> ExprAt s ns
  (.e) (MkAnnotAt ty sort) s = MkExpr ty (MkAnnotAt sort s)


-- Helper to decide which `Expr` to pick based on an optional stage
public export
0 ExprAtMaybe : Maybe Stage -> Ctx -> Type
ExprAtMaybe Nothing = Expr
ExprAtMaybe (Just s) = ExprAt s

-- Turn `ExprAtMaybe` into `Expr`
public export
(.mp) : {s : Maybe Stage} -> ExprAtMaybe s ns -> Expr ns
(.mp) {s = Just s} (MkExpr tm (MkAnnotAt ty sort)) = MkExpr tm (MkAnnot ty sort s)
(.mp) {s = Nothing} x = x

-- Operations
public export
Op : Arity -> Ctx -> Type
Op ar ns = (Tel ar Annot ns, Annot (ns ::< ar))
  
public export covering
Relabel Annot where
  relabel r (MkAnnot ty sort s) = MkAnnot (relabel r ty) (relabel r sort) s
  
public export covering
Thin Annot where
  thin r (MkAnnot ty sort s) = MkAnnot (thin r ty) (thin r sort) s

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
Thin (AnnotAt s) where
  thin r (MkAnnotAt ty sort) = MkAnnotAt (thin r ty) (thin r sort)

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
Thin Expr where
  thin r (MkExpr t a) = MkExpr (thin r t) (thin r a)

public export covering
WeakSized Expr where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalSized Atom Expr Expr where
  evalS env (MkExpr tm a) = MkExpr (evalS env tm) (evalS env a)

public export covering
Relabel (ExprAt s) where
  relabel r (MkExpr t a) = MkExpr (relabel r t) (relabel r a)

public export covering
Thin (ExprAt s) where
  thin r (MkExpr t a) = MkExpr (thin r t) (thin r a)

public export covering
WeakSized (ExprAt s) where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalSized Atom (ExprAt s) (ExprAt s) where
  evalS env (MkExpr tm a) = MkExpr (evalS env tm) (evalS env a)

public export covering
[relabelExprAtMaybe] {s : Maybe Stage} -> Relabel (ExprAtMaybe s) where
  relabel {s = Just s} r e = relabel {tm = ExprAt s} r e
  relabel {s = Nothing} r e = relabel {tm = Expr} r e

public export covering
[thinExprAtMaybe] {s : Maybe Stage} -> Thin (ExprAtMaybe s) where
  thin {s = Just s} r e = thin {tm = ExprAt s} r e
  thin {s = Nothing} r e = thin {tm = Expr} r e

public export covering
[weakExprAtMaybe] {s : Maybe Stage} -> WeakSized (ExprAtMaybe s) where
  weakS {s = Just s} e t = weakS {tm = ExprAt s} e t
  weakS {s = Nothing} e t = weakS {tm = Expr} e t

public export covering
[evalExprAtMaybe] {s : Maybe Stage} -> EvalSized Atom (ExprAtMaybe s) (ExprAtMaybe s) where
  evalS {s = Just s} e t = evalS {tm = ExprAt s} e t
  evalS {s = Nothing} e t = evalS {tm = Expr} e t

public export covering
Relabel (Op ar) where
  relabel r (a, b) = (relabel r a, relabel (keepMany r) b)

public export covering
Thin (Op ar) where
  thin r (a, b) = (thin r a, thin {sms = sms + a.count} {sns = sns + a.count} (keepMany r) b)
  
export covering
Show (Term Syntax ns) => Show (Atom ns) where
  show a = show a.syn
  
export covering
Show (Spine ar (Term Syntax) ns) => Show (Spine ar Atom ns) where
  show a = show a.syn