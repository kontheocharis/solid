-- Unification for values in the core language
module Core.Unification

import Utils
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

-- Unification

-- Unification outcome
--
-- Observationally means under all substitutions from the empty context.
public export
data Unification : Type where
  -- Are observationally the same
  AreSame : Unification
  -- Are observationally different
  AreDifferent : Unification
  -- Don't look the same but could become the same (or different) under
  -- appropriate substitutions
  DontKnow : Unification

-- Whether we are allowed to solve metavariables in a given context.
data SolvingMode : Type where
  SolvingAllowed : SolvingMode
  SolvingNotAllowed : SolvingMode

-- A monad for metavariable solving.
public export
interface (forall sm . Monad (m sm)) => HasMetas (0 m : SolvingMode -> Type -> Type) where
  -- Get the solution of a metavariable, if any.
  getMeta : MetaVar -> m sm (Maybe (Term Value [<]))

  -- Check if we are allowed to solve metavariables.
  canSolve : m sm (Singleton sm)

  -- Solve a metavariable.
  solve : MetaVar -> Term Value [<] -> m SolvingAllowed ()

  -- Switch to a context where we are not allowed to solve metavariables.
  noSolving : m SolvingNotAllowed a -> m sm a

-- The typeclass for unification
--
-- The monad is indexed over if we are allowed to solve metavariables.
public export
interface (HasMetas m) => Unify m sm (0 lhs : Ctx -> Type) (0 rhs : Ctx -> Type) where
  unify : Size ns -> lhs ns -> rhs ns -> m sm Unification

-- Definitively decide a unification outcome based on a decidable equality
public export
ifAndOnlyIf : Monad m => Dec (a ~=~ b) -> ((a ~=~ b) -> m Unification) -> m Unification
ifAndOnlyIf (Yes Refl) f = f Refl
ifAndOnlyIf (No _) _ = pure AreDifferent

-- Definitively decide a unification outcome based on a semi-decidable equality
--
-- This is a "hack" because really we should be providing DecEq to be sure they
-- are different. However sometimes it is super annoying to implement DecEq so
-- we just use this instead.
public export
ifAndOnlyIfHack : Monad m => Maybe (a ~=~ b) -> ((a ~=~ b) -> m Unification) -> m Unification
ifAndOnlyIfHack (Just Refl) f = f Refl
ifAndOnlyIfHack Nothing _ = pure AreDifferent

-- Partially decide a unification outcome based on a semi-decidable equality
public export
inCase : Monad m => Maybe (a ~=~ b) -> ((a ~=~ b) -> m Unification) -> m Unification
inCase (Just Refl) f = f Refl
inCase Nothing _ = pure DontKnow

export infixr 5 /\
export infixr 4 \/

-- Conjunction of unification outcomes (fully monadic version)
public export
(/\) : (Monad m) => m Unification -> m Unification -> m Unification
mx /\ my = do
  x <- mx
  case x of
    AreDifferent => pure AreDifferent
    AreSame => my
    DontKnow => do
      y <- my
      case y of
        AreSame => pure DontKnow
        AreDifferent => pure AreDifferent
        DontKnow => pure DontKnow

-- Disjunction of unification outcomes (fully monadic version)
public export
(\/) : (Monad m) => m Unification -> m Unification -> m Unification
mx \/ my = do
  x <- mx
  case x of
    AreSame => pure AreSame
    AreDifferent => my
    DontKnow => do
      y <- my
      case y of
        AreSame => pure AreSame
        AreDifferent => pure DontKnow
        DontKnow => pure DontKnow

-- Basic implementations

public export
HasMetas m => Unify m sm Lvl Lvl where
  unify s l l' = ifAndOnlyIf (decEq l l') (\Refl => pure AreSame)

public export
(HasMetas m, Unify m sm val val') => Unify m sm (Spine as val) (Spine as' val') where
  unify s [] [] = pure AreSame
  unify s (x :: xs) (y :: ys) = unify s x y /\ unify s xs ys
  unify s _ _ = pure AreDifferent

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

HasMetas m => Unify m sm (Term Value) (Term Value)

-- Unification outcome depends on reducibility
--
-- Must also be in the same stage to be unifiable.
{r, r' : Reducibility} -> HasMetas m => Unify m sm (Binder md r Value n) (Binder md r' Value n') where
  unify _ (BindLam _) (BindLam _) = pure AreSame
  unify s (BindLet _ tyA a) (BindLet _ tyB b) = (unify s tyA tyB /\ unify s a b) \/ pure DontKnow
  unify s (BindPi _ a) (BindPi _ b) = unify s a b
  unify {r = Rigid} {r' = Rigid} _ _ _ = pure AreDifferent
  unify _ _ _ = pure DontKnow

HasMetas m => Unify m SolvingNotAllowed (Variable Value) (Variable Value) where
  unify s (Level l) (Level l') = unify s l l'

HasMetas m => Unify m sm (Body Value n) (Body Value n') where
  unify s (Closure {n = n} envA tA) (Closure envB tB)
    = unify {lhs = Term Value} {rhs = Term Value} (SS {n = n} s)
      (eval (lift s envA) tA)
      (eval (lift s envB) tB)

{r, r' : Reducibility} -> HasMetas m => Unify m sm (Binding md r Value) (Binding md r' Value) where
  unify s (Bound md bindA bodyA) (Bound md bindB bodyB)
    = unify s bindA bindB /\ unify s bodyA bodyB

{hk : PrimitiveClass} -> HasMetas m => Unify m sm (PrimitiveApplied hk Value Simplified) (PrimitiveApplied hk Value Simplified) where
  unify s (SimpApplied {r = PrimIrreducible} p sp) (SimpApplied {r = PrimIrreducible} p' sp')
    = ifAndOnlyIfHack (primEq p p') (\Refl => unify s sp sp')
  unify s (SimpApplied p sp) (SimpApplied p' sp')
    = noSolving (inCase (primEq p p') (\Refl => unify s sp sp') \/ pure DontKnow)

{hk : PrimitiveClass} -> HasMetas m => Unify m SolvingNotAllowed (PrimitiveApplied hk Value Normalised) (PrimitiveApplied hk Value Normalised) where
  -- conservative
  unify s (LazyApplied p sp gl) (LazyApplied p' sp' gl')
    = inCase (primEq p p') (\Refl => unify s sp sp') \/ pure DontKnow

HasMetas m => Unify m SolvingNotAllowed (Head Value Simplified) (Head Value Simplified) where
  -- conservative for meta solutions
  unify s (ValVar v) (ValVar v') = unify s v v'
  unify s (ValMeta m) (ValMeta m') = inCase (decToSemiDec (decEq m m')) (\Refl => pure AreSame)
  unify s (PrimNeutral p) (PrimNeutral p') = unify s p p'
  unify s _ _ = pure DontKnow

HasMetas m => Unify m sm (HeadApplied Value Simplified) (HeadApplied Value Simplified) where
  unify s (h $$ sp) (h' $$ sp') = (noSolving (unify s h h') /\ unify s sp sp') \/ pure DontKnow

HasMetas m => Unify m SolvingNotAllowed (Head Value Normalised) (Head Value Normalised) where
  -- conservative
  unify s (ObjCallable a) (ObjCallable a') = unify s a a'
  unify s (ObjLazy a) (ObjLazy b) = unify s a b
  unify s (PrimNeutral p) (PrimNeutral p') = noSolving (unify s p p')
  unify _ _ _ = pure DontKnow

HasMetas m => Unify m SolvingNotAllowed (HeadApplied Value Normalised) (HeadApplied Value Normalised) where
  -- conservative
  unify s (h $$ sp) (h' $$ sp') = (unify s h h' /\ unify s sp sp') \/ pure DontKnow

HasMetas m => Unify m SolvingNotAllowed LazyValue LazyValue where
  -- conservative
  unify s (LazyApps h sp) (LazyApps h' sp') = (unify s h h' /\ unify s sp sp') \/ pure DontKnow
  unify s (LazyPrimNormal p) (LazyPrimNormal p') = unify s p p'
  unify _ _ _ = pure DontKnow

-- Finally, term unification

HasMetas m => Unify m sm (Term Value) (Term Value) where
  unify s (MtaCallable m) (MtaCallable m') = unify s m m'
  unify s (SimpPrimNormal p) (SimpPrimNormal p') = unify s p p'
  unify s (SimpObjCallable o) (SimpObjCallable o') = unify s o o'
  unify s (RigidBinding md r) (RigidBinding md' r') = ifAndOnlyIf (decEq md md') (\Refl => unify s r r')

  unify s a (SimpApps (ValMeta m $$ sp)) = ?rhs
  unify s (SimpApps (ValMeta m $$ sp)) b = ?rhs2

  -- glued terms can reduce further
  unify s (Glued a) (Glued b) = noSolving (unify s a b) \/ unify s (simplified a) (simplified b)
  unify s a (Glued b) = unify s a (simplified b)
  unify s (Glued a) b = unify s (simplified a) b

  -- simplified (rigid) applications
  unify s (SimpApps a) (SimpApps a') = unify s a a'
  unify _ (SimpApps _) _ = pure DontKnow
  unify _ _ (SimpApps _) = pure DontKnow

  -- everything else is different
  unify _ _ _ = pure AreDifferent
