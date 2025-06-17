-- Unification for values in the core language
module Core.Unification

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Primitives
import Core.Syntax
import Core.Evaluation
import Core.Rules
import Core.Metavariables

%default covering

-- Unification

-- Unification outcome
--
-- Observationally means under all substitutions from the empty context.
public export
data Unification : Ctx -> Type where
  -- Are observationally the same
  AreSame : Unification ns
  -- Are observationally different
  AreDifferent : Unification ns
  -- Can't really tell; could become the same (or different) under
  -- appropriate substitutions
  DontKnow : Unification ns
  -- An error occurred while solving a metavariable
  -- Also remembers all the extra binders we were solving under.
  Error : {under : Arity} -> SolveError (ns ::< under) -> Unification ns

-- Escape a unification result under a binder, by storing the binder name
-- in the result.
--
-- If the binder didn't have a name, we just use the name `_` which stands for
-- "internal binder".
escapeBinder : Maybe (Singleton n) -> Unification (ns :< n) -> Unification ns
escapeBinder sn AreSame = AreSame
escapeBinder sn AreDifferent = AreDifferent
escapeBinder sn DontKnow = DontKnow
escapeBinder (Just (Val n)) (Error {under = ar} err) = Error {under = n :: ar} err
escapeBinder Nothing (Error {under = ar} err) = Error {under = (Explicit, "_") :: ar} ?err

-- The typeclass for unification
--
-- The monad is indexed over if we are allowed to solve metavariables.
public export
interface Unify sm (0 lhs : Ctx -> Type) (0 rhs : Ctx -> Type) where
  -- Resolve any metas in terms, no-op by default
  resolveLhs : (HasMetas m) => lhs ns -> m sm (lhs ns)
  resolveLhs x = pure x
  resolveRhs : (HasMetas m) => rhs ns -> m sm (rhs ns)
  resolveRhs x = pure x

  -- Unify two terms, given the size of the context, assuming both sides are
  -- already resolved
  unifyImpl : (HasMetas m) => Size ns => lhs ns -> rhs ns -> m sm (Unification ns)

-- The actual unification function, first resolves both sides.
public export
unify : HasMetas m => Unify sm lhs rhs => Size ns => lhs ns -> rhs ns -> m sm (Unification ns)
unify @{_} @{u} @{s} l r = do
  l' <- resolveLhs @{u} l
  r' <- resolveRhs @{u} r
  unifyImpl l' r'

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
solve : HasMetas m => Size ns
  => MetaVar
  -> Spine ar (Term Value) ns
  -> Term Value ns
  -> m sm (Unification ns)
solve m sp t = canSolve >>= \case
  Val SolvingAllowed => solveProblem (MkFlex m sp) t >>= \case
    Left err => pure $ Error {under = []} err
    Right () => pure AreSame
  Val SolvingNotAllowed => pure DontKnow

-- Basic implementations

public export
Unify sm Lvl Lvl where
  unifyImpl l l' = ifAndOnlyIf (decEq l l') (\Refl => pure AreSame)

public export
Unify sm val val' => Unify sm (Spine as val) (Spine as' val') where
  unifyImpl [] [] = pure AreSame
  unifyImpl ((_, x) :: xs) ((_, y) :: ys) = unify x y /\ unify xs ys
  unifyImpl _ _ = pure AreDifferent

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

Unify sm (Term Value) (Term Value)

-- Unification outcome depends on reducibility
-- Conservative for lets.
--
-- Must also be in the same stage to be unifiable.
{sm : SolvingMode} -> {r, r' : Reducibility} -> Unify sm (Binder md r Value n) (Binder md r' Value n') where
  unifyImpl (BindMtaLam _) (BindMtaLam _) = pure AreSame
  -- unification presupposes same-typedness of both sides so we don't need to check the data here
  unifyImpl (BindObjLam _ _ _) (BindObjLam _ _ _) = pure AreSame
  unifyImpl (BindMtaLet _ tyA a) (BindMtaLet _ tyB b) = noSolving ((unify tyA tyB /\ unify a b) \/ pure DontKnow)
  -- same here
  unifyImpl (BindObjLet _ _ tyA a) (BindObjLet _ _ tyB b) = noSolving ((unify tyA tyB /\ unify a b) \/ pure DontKnow)
  unifyImpl (BindMtaPi _ a) (BindMtaPi _ b) = unify a b
  unifyImpl (BindObjPi _ ba bb a) (BindObjPi _ ba' bb' a') = unify ba ba' /\ unify bb bb' /\ unify a a'
  unifyImpl {r = Rigid} {r' = Rigid} _ _ = pure AreDifferent
  unifyImpl _ _ = pure DontKnow

Unify SolvingNotAllowed (Variable Value) (Variable Value) where
  unifyImpl (Level l) (Level l') = unify l l'

{sm : SolvingMode} -> {r, r' : Reducibility} -> Unify sm (Binding md r Value) (Binding md r' Value) where
  unifyImpl (Bound md bindA (Closure {n = n} envA tA)) (Bound md bindB (Closure envB tB))
    -- unify the binders
    = unify bindA bindB
      -- unify the bodies, retaining the name of the first binder (kind of arbirary..)
      /\ (escapeBinder (displayIdent bindA) <$> unify {lhs = Term Value} {rhs = Term Value}
          (eval (lift envA) tA)
          (eval (lift envB) tB))

{sm : SolvingMode} -> {hk : PrimitiveClass} ->
  Unify sm (PrimitiveApplied hk Value Simplified) (PrimitiveApplied hk Value Simplified) where
    unifyImpl (SimpApplied {r = PrimIrreducible} p sp) (SimpApplied {r = PrimIrreducible} p' sp')
      = ifAndOnlyIfHack (primEq p p') (\Refl => unify sp sp')
    unifyImpl (SimpApplied p sp) (SimpApplied p' sp')
      = noSolving (inCase (primEq p p') (\Refl => unify sp sp') \/ pure DontKnow)

{hk : PrimitiveClass} ->
  Unify SolvingNotAllowed (PrimitiveApplied hk Value Normalised) (PrimitiveApplied hk Value Normalised) where
    -- conservative
    unifyImpl (LazyApplied p sp gl) (LazyApplied p' sp' gl')
      = inCase (primEq p p') (\Refl => unify sp sp') \/ pure DontKnow

Unify SolvingNotAllowed (Head Value Simplified) (Head Value Simplified) where
  -- conservative for meta solutions
  unifyImpl (ValVar v) (ValVar v') = unify v v'
  unifyImpl (ValMeta m) (ValMeta m') = inCase (decToSemiDec (decEq m m')) (\Refl => pure AreSame)
  unifyImpl (PrimNeutral p) (PrimNeutral p') = unify p p'
  unifyImpl _ _ = pure DontKnow

{sm : SolvingMode} -> Unify sm (HeadApplied Value Simplified) (HeadApplied Value Simplified) where
  -- will never retry from this so it's fine to say DontKnow in the end
  unifyImpl (h $$ sp) (h' $$ sp') = (noSolving (unify h h') /\ unify sp sp') \/ pure DontKnow

Unify SolvingNotAllowed (Head Value Normalised) (Head Value Normalised) where
  -- conservative
  unifyImpl (ObjCallable a) (ObjCallable a') = unify a a'
  unifyImpl (ObjLazy a) (ObjLazy b) = unify a b
  unifyImpl (ValDef v) (ValDef v') = unify v v'
  unifyImpl (PrimNeutral p) (PrimNeutral p') = noSolving (unify p p')
  unifyImpl _ _ = pure DontKnow

Unify SolvingNotAllowed (HeadApplied Value Normalised) (HeadApplied Value Normalised) where
  -- conservative
  unifyImpl (h $$ sp) (h' $$ sp') = (unify h h' /\ unify sp sp') \/ pure DontKnow

Unify SolvingNotAllowed LazyValue LazyValue where
  -- conservative
  unifyImpl (LazyApps h _) (LazyApps h' _) = unify h h' \/ pure DontKnow
  unifyImpl (LazyPrimNormal p) (LazyPrimNormal p') = unify p p'
  unifyImpl _ _ = pure DontKnow

-- Finally, term unification
export
[unifyValues] {sm : SolvingMode} -> (HasMetas m) => Unify sm (Term Value) (Term Value) where
  resolveLhs = resolveMetas
  resolveRhs = resolveMetas

  unifyImpl (MtaCallable m) (MtaCallable m') = unify m m'
  unifyImpl (SimpPrimNormal p) (SimpPrimNormal p') = unify p p'
  unifyImpl (SimpObjCallable o) (SimpObjCallable o') = unify o o'
  unifyImpl (RigidBinding md r) (RigidBinding md' r') = ifAndOnlyIf (decEq md md') (\Refl => unify r r')

  -- Solve metas
  unifyImpl a (SimpApps (ValMeta m' $$ sp')) = solve m' sp' a
  unifyImpl (SimpApps (ValMeta m $$ sp)) b = solve m sp b

  -- glued terms can reduce further
  unifyImpl (Glued a) (Glued b) = noSolving (unify a b) \/ unify (simplified a) (simplified b)
  unifyImpl a (Glued b) = unify a (simplified b)
  unifyImpl (Glued a) b = unify (simplified a) b

  -- simplified (rigid) applications
  unifyImpl (SimpApps a) (SimpApps a') = unify a a'
  unifyImpl (SimpApps _) _ = pure DontKnow
  unifyImpl _ (SimpApps _) = pure DontKnow

  -- everything else is different
  unifyImpl _ _ = pure AreDifferent
