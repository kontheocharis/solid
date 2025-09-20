-- Unification for values in the core language
module Core.Unification

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Metavariables
import Core.Atoms
import Core.Context

%default covering

-- Unification

-- Unification outcome
public export
data Unification : Ctx -> Type where
  -- Are the same
  AreSame : Unification ns
  -- Are different
  AreDifferent : Unification ns
  -- Could become the same (or different) under
  -- appropriate substitutions
  DontKnow : Unification ns
  -- An error occurred while solving a metavariable
  -- Also remembers all the extra binders we were solving under.
  Error : {under : Arity} -> SolveError (ns ::< under) -> Unification ns
  
export
(ns : Ctx) => ShowSyntax => Show (Unification ns) where
  show AreSame = "terms are the same"
  show AreDifferent = "terms are different"
  show DontKnow = "terms are not the same"
  show (Error x) = "unification error: \{show x}"

-- Escape a unification result under a binder, by storing the binder name
-- in the result.
--
-- If the binder didn't have a name, we just use the name `_` which stands for
-- "internal binder".
escapeBinder : Size ns => Maybe (Singleton n) -> Unification (ns :< n) -> Unification ns
escapeBinder sn AreSame = AreSame
escapeBinder sn AreDifferent = AreDifferent
escapeBinder sn DontKnow = DontKnow
escapeBinder (Just (Val n)) (Error {under = ar} err) = Error {under = n :: ar} err
escapeBinder Nothing (Error {under = ar} err)
  = Error {under = (Explicit, "_") :: ar} (relabel (keepMany @{ar.count} (Change _ Id)) err)

-- The typeclass for unification
--
-- The monad is indexed over if we are allowed to solve metavariables.
public export
interface Unify sm (0 lhs : Ctx -> Type) (0 rhs : Ctx -> Type) where
  -- Resolve any metas in terms, no-op by default
  resolveLhs : (HasMetas m) => Scope bs Atom ns -> lhs ns -> m sm (lhs ns)
  resolveLhs _ x = pure x
  resolveRhs : (HasMetas m) => Scope bs Atom ns -> rhs ns -> m sm (rhs ns)
  resolveRhs _ x = pure x

  -- Unify two terms, given the size of the context, assuming both sides are
  -- already resolved
  unifyImpl : (HasMetas m) => Size ns => Scope bs Atom ns -> lhs ns -> rhs ns -> m sm (Unification ns)

-- The actual unification function, first resolves both sides.
public export
unify : HasMetas m => Unify sm lhs rhs => Scope bs Atom ns -> lhs ns -> rhs ns -> m sm (Unification ns)
unify @{_} @{u} ctx l r = do
  l' <- resolveLhs @{u} ctx l
  r' <- resolveRhs @{u} ctx r
  unifyImpl ctx l' r'

-- Definitively decide a unification outcome based on a decidable equality
public export
ifAndOnlyIf : Monad m => Dec (a ~=~ b) -> ((a ~=~ b) -> m (Unification ns)) -> m (Unification ns)
ifAndOnlyIf (Yes Refl) f = f Refl
ifAndOnlyIf (No _) _ = pure AreDifferent

-- Definitively decide a unification outcome based on a semi-decidable equality
--
-- This is a "hack" because really we should be providing DecEq to be sure they
-- are different. However sometimes it is super annoying to implement DecEq so
-- we just use this instead.
public export
ifAndOnlyIfHack : Monad m => Maybe (a ~=~ b) -> ((a ~=~ b) -> m (Unification ns)) -> m (Unification ns)
ifAndOnlyIfHack (Just Refl) f = f Refl
ifAndOnlyIfHack Nothing _ = pure AreDifferent

-- Partially decide a unification outcome based on a semi-decidable equality
public export
inCase : Monad m => Maybe (a ~=~ b) -> ((a ~=~ b) -> m (Unification ns)) -> m (Unification ns)
inCase (Just Refl) f = f Refl
inCase Nothing _ = pure DontKnow

export infixr 5 /\
export infixr 4 \/

-- Conjunction of unification outcomes (fully monadic version)
public export
(/\) : (Monad m) => m (Unification ns) -> m (Unification ns) -> m (Unification ns)
mx /\ my = do
  x <- mx
  case x of
    Error e => pure $ Error e
    AreDifferent => pure AreDifferent
    AreSame => my
    DontKnow => pure $ DontKnow

-- Disjunction of unification outcomes (fully monadic version)
public export
(\/) : (Monad m) => m (Unification ns) -> m (Unification ns) -> m (Unification ns)
mx \/ my = do
  x <- mx
  case x of
    -- errors always propagate, even in disjunction, because otherwise we might
    -- partially solve a problem and then fail, then continue in an alternative branch
    Error e => pure $ Error e
    AreSame => pure AreSame
    AreDifferent => my
    DontKnow => my

-- Solve a unification problem if possible, and return an appropriate outcome
solve : forall bs . HasMetas m => Size ns
  => Scope bs Atom ns
  -> MetaVar
  -> Spine ar (Term Value) ns
  -> Term Value ns
  -> m sm (Unification ns)
solve sc m sp t = canSolve >>= \case
  Val SolvingAllowed => 
    -- First expand all context names from the given scope
    let expand = sc.defs.asSub in
    let inv = sc.defs.inv in
    let sp' = sub expand (promoteSpine sp) in
    let t' = sub expand (promote t) in
    solveProblem (MkFlex m sp'.val) t'.val >>= \case
      Left err => pure $ Error {under = []} (thin inv err)
      Right () => pure AreSame
  Val SolvingNotAllowed => pure DontKnow

-- Resolve variables from a scope
export
varResolver : Monad m => Scope bs Atom ns -> Resolver m (Val ns)
varResolver sc = repeatedly $ \case
  SimpApps (ValVar (Level x) $$ sp) => case getDef sc x of
    Just tm => pure $ Just (apps tm.val sp)
    Nothing => pure Nothing
  _ => pure Nothing

export
gluedVarResolver : Monad m => Scope bs Atom ns -> Resolver m (Val ns)
gluedVarResolver sc = repeatedly $ \case
  SimpApps (ValVar (Level x) $$ sp) => case getDef sc x of
    Just tm => pure $ Just (Glued (LazyApps (ValVarWithDef (Level x) $$ sp) (apps tm.val sp)))
    Nothing => pure Nothing
  _ => pure Nothing

-- Basic implementations

public export
Unify sm Lvl Lvl where
  unifyImpl ctx l l' = ifAndOnlyIf (decEq l l') (\Refl => pure AreSame)

public export
Unify sm vl vl' => Unify sm (Spine as vl) (Spine as' vl') where
  unifyImpl ctx [] [] = pure AreSame
  unifyImpl ctx ((_, x) :: xs) ((_, y) :: ys) = unify ctx x y /\ unify ctx xs ys
  unifyImpl ctx _ _ = pure AreDifferent

-- Note: a lot of the intermediate unification implementations might return
-- DontKnow for things that are actually the same--they do not actually
-- perform any reductions for a proper check. In other words they are quite
-- conservative.
--
-- For example, the LazyValue unification does not try to reduce lazy apps,
-- it just returns DontKnow if they mismatch. It is up to the caller to then
-- perform the appropriate reduction. This also includes all `normalised` (but
-- not simplified) things.
--
-- All such conservative operations are never allowed to solve metavariables.

export
%hint
unifyValues : {sm : SolvingMode} -> Unify sm (Term Value) (Term Value)

-- Unification outcome depends on reducibility
-- Conservative for lets.
--
-- Must also be in the same stage to be unifiable.
{sm : SolvingMode} -> {r, r' : Reducibility} -> Unify sm (Binder md r Value n) (Binder md r' Value n') where
  unifyImpl ctx (BindMtaLam _) (BindMtaLam _) = pure AreSame
  -- unification presupposes same-typedness of both sides so we don't need to check the data here
  unifyImpl ctx (BindObjLam _ _ _) (BindObjLam _ _ _) = pure AreSame
  unifyImpl ctx (BindMtaLet _ tyA a) (BindMtaLet _ tyB b) = noSolving ((unify ctx tyA tyB /\ unify ctx a b) \/ pure DontKnow)
  -- same here
  unifyImpl ctx (BindObjLet _ _ tyA a) (BindObjLet _ _ tyB b) = noSolving ((unify ctx tyA tyB /\ unify ctx a b) \/ pure DontKnow)
  unifyImpl ctx (BindMtaPi _ a) (BindMtaPi _ b) = unify ctx a b
  unifyImpl ctx (BindObjPi _ ba bb a) (BindObjPi _ ba' bb' a') = unify ctx ba ba' /\ unify ctx bb bb' /\ unify ctx a a'
  unifyImpl ctx {r = Rigid} {r' = Rigid} _ _ = pure AreDifferent
  unifyImpl ctx _ _ = pure DontKnow

Unify SolvingNotAllowed (Variable Value) (Variable Value) where
  unifyImpl ctx (Level l) (Level l') = unify ctx l l'

{sm : SolvingMode} -> {r, r' : Reducibility} -> Unify sm (Binding md r Value) (Binding md r' Value) where
  unifyImpl ctx (Bound md bindA (Closure {n = n} envA tA)) (Bound md bindB (Closure envB tB))
    -- unify ctx the binders
    = unify ctx bindA bindB
      -- unify ctx the bodies, retaining the name of the first binder (kind of arbirary..)
      /\ (escapeBinder (displayIdent bindA) <$> unify (lift {a = n} ctx) {lhs = Term Value} {rhs = Term Value}
          (eval (lift envA) tA)
          (eval (lift envB) tB))

{sm : SolvingMode} -> {hk : PrimitiveClass} ->
  Unify sm (PrimitiveApplied hk Value Simplified) (PrimitiveApplied hk Value Simplified) where
    unifyImpl ctx (SimpApplied {r = PrimIrreducible} p sp) (SimpApplied {r = PrimIrreducible} p' sp')
      = ifAndOnlyIfHack (primEq p p') (\Refl => unify ctx sp sp')
    unifyImpl ctx (SimpApplied p sp) (SimpApplied p' sp')
      = noSolving (inCase (primEq p p') (\Refl => unify ctx sp sp') \/ pure DontKnow)

{hk : PrimitiveClass} ->
  Unify SolvingNotAllowed (PrimitiveApplied hk Value Normalised) (PrimitiveApplied hk Value Normalised) where
    -- conservative
    unifyImpl ctx (LazyApplied p sp gl) (LazyApplied p' sp' gl')
      = inCase (primEq p p') (\Refl => unify ctx sp sp') \/ pure DontKnow

Unify SolvingNotAllowed (Head Value Simplified) (Head Value Simplified) where
  -- conservative for meta solutions
  unifyImpl ctx (ValVar v) (ValVar v') = unify ctx v v'
  unifyImpl ctx (ValMeta m) (ValMeta m') = inCase (decToSemiDec (decEq m m')) (\Refl => pure AreSame)
  unifyImpl ctx (PrimNeutral p) (PrimNeutral p') = unify ctx p p'
  unifyImpl ctx _ _ = pure DontKnow

{sm : SolvingMode} -> Unify sm (HeadApplied Value Simplified) (HeadApplied Value Simplified) where
  -- will never retry from this so it's fine to say DontKnow in the end
  unifyImpl ctx (h $$ sp) (h' $$ sp') = (noSolving (unify ctx h h') /\ unify ctx sp sp') \/ pure DontKnow

Unify SolvingNotAllowed (Head Value Normalised) (Head Value Normalised) where
  -- conservative
  unifyImpl ctx (ValVarWithDef v) (ValVarWithDef v') = unify ctx v v'
  unifyImpl ctx (ObjCallable a) (ObjCallable a') = unify ctx a a'
  unifyImpl ctx (ObjLazy a) (ObjLazy b) = unify ctx a b
  unifyImpl ctx (PrimNeutral p) (PrimNeutral p') = noSolving (unify ctx p p')
  unifyImpl ctx _ _ = pure DontKnow

Unify SolvingNotAllowed (HeadApplied Value Normalised) (HeadApplied Value Normalised) where
  -- conservative
  unifyImpl ctx (h $$ sp) (h' $$ sp') = (unify ctx h h' /\ unify ctx sp sp') \/ pure DontKnow

Unify SolvingNotAllowed LazyValue LazyValue where
  -- conservative
  unifyImpl ctx (LazyApps h _) (LazyApps h' _) = unify ctx h h' \/ pure DontKnow
  unifyImpl ctx (LazyPrimNormal p) (LazyPrimNormal p') = unify ctx p p'
  unifyImpl ctx _ _ = pure DontKnow

-- Finally, term unification
export
[unifyValues] {sm : SolvingMode} -> Unify sm (Term Value) (Term Value) where
  -- @@Todo: short-circuit some glued stuff (metas + vars) here
  resolveLhs ctx x = resolve (metaResolver <+> gluedVarResolver ctx <+> primResolver) x
  resolveRhs ctx x = resolve (metaResolver <+> gluedVarResolver ctx <+> primResolver) x

  unifyImpl ctx (MtaCallable m) (MtaCallable m') = unify ctx m m'
  unifyImpl ctx (SimpPrimNormal p) (SimpPrimNormal p') = unify ctx p p'
  unifyImpl ctx (SimpObjCallable o) (SimpObjCallable o') = unify ctx o o'
  unifyImpl ctx (RigidBinding md r) (RigidBinding md' r') = ifAndOnlyIf (decEq md md') (\Refl => unify ctx r r')

  -- Solve metas
  unifyImpl ctx a (SimpApps (ValMeta m' $$ sp')) = solve ctx m' sp' a
  unifyImpl ctx (SimpApps (ValMeta m $$ sp)) b = solve ctx m sp b

  -- glued terms can reduce further
  unifyImpl ctx (Glued a) (Glued b) = noSolving (unify ctx a b) \/ unify ctx (simplified a) (simplified b)
  unifyImpl ctx a (Glued b) = unify ctx a (simplified b)
  unifyImpl ctx (Glued a) b = unify ctx (simplified a) b

  -- simplified (rigid) applications
  unifyImpl ctx (SimpApps a) (SimpApps a') = unify ctx a a'
  unifyImpl ctx (SimpApps _) _ = pure DontKnow
  unifyImpl ctx _ (SimpApps _) = pure DontKnow

  -- everything else is different
  unifyImpl ctx _ _ = pure AreDifferent

-- Atom unification
export
{sm : SolvingMode} -> Unify sm Atom Atom where
  unifyImpl ctx a b = unify ctx a.val b.val