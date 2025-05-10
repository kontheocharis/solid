-- Unification for values in the core language
module Core.Unification

import Utils
import Decidable.Equality
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

Unify (Term Value) (Term Value)

-- Unification outcome depends on reducibility
-- Must also be in the same stage to be unifiable.
{r, r' : Reducibility} -> Unify (Binder md r Value) (Binder md r' Value) where
  unify _ BindLam BindLam = AreSame
  unify s (BindLet tyA a) (BindLet tyB b) = unify s tyA tyB /\ unify s a b
  unify s (BindPi a) (BindPi b) = unify s a b
  unify {r = Rigid} {r' = Rigid} _ _ _ = AreDifferent
  unify _ _ _ = DontKnow

Unify (Variable Value) (Variable Value) where
  unify s (Level l) (Level l') = unify s l l'

Unify (Body Value n) (Body Value n') where
  unify s (Closure {n = n} envA tA) (Closure envB tB)
    = unify {lhs = Term Value} {rhs = Term Value} (SS {n = n} s)
      (eval (lift s envA) tA)
      (eval (lift s envB) tB)

{r, r' : Reducibility} -> Unify (Binding md r Value) (Binding md r' Value) where
  unify s (Bound md n bindA bodyA) (Bound md n' bindB bodyB)
    = unify s bindA bindB /\ unify s bodyA bodyB

{hk : PrimitiveClass} -> Unify (PrimitiveApplied hk Value Simplified) (PrimitiveApplied hk Value Simplified) where
  unify s (SimpApplied {r = PrimIrreducible} p sp) (SimpApplied {r = PrimIrreducible} p' sp')
    = ifAndOnlyIfHack (primEq p p') (\Refl => unify s sp sp')
  unify s (SimpApplied p sp) (SimpApplied p' sp')
    = inCase (primEq p p') (\Refl => unify s sp sp')

Unify (Head Value Simplified) (Head Value Simplified) where
  unify s (ValVar v) (ValVar v') = unify s v v'
  unify s (ValMeta m) (ValMeta m') = ?metasBro
  unify s (PrimNeutral p) (PrimNeutral p') = unify s p p'
  unify s _ _ = DontKnow

Unify (HeadApplied Value Simplified) (HeadApplied Value Simplified) where
  unify s (h $$ sp) (h' $$ sp') = unify s h h' /\ unify s sp sp'

Unify LazyValue LazyValue where
  unify s (LazyApps h sp) (LazyApps h' sp') = ?fx /\ unify s sp sp'
  unify s (LazyPrimNormal p) (LazyPrimNormal p') = ?fy
  unify s (LazyApps h sp) (LazyPrimNormal p') = ?fz
  unify s (LazyPrimNormal p) (LazyApps h' sp') = ?fw

Unify (Term Value) (Term Value) where
  unify s (SimpApps a) (SimpApps a') = unify s a a'
  unify s (MtaCallable m) (MtaCallable m') = unify s m m'
  unify s (SimpPrimNormal p) (SimpPrimNormal p') = unify s p p'
  unify s (SimpObjCallable o) (SimpObjCallable o') = unify s o o'
  unify s (RigidBinding md r) (RigidBinding md' r') = ifAndOnlyIf (decEq md md') (\Refl => unify s r r')

  -- glued stuff
  unify s (Glued a) (Glued b) = unify s a b `orTry` unify s (simplified a) (simplified b)
  unify s a (Glued b) = unify s a (simplified b)
  unify s (Glued a) b = unify s (simplified a) b

  -- i dont know
  unify _ (SimpApps _) _ = DontKnow
  unify _ _ (SimpApps _) = DontKnow

  -- everything else is different
  unify _ _ _ = AreDifferent

  -- unify _ (RigidBinding _ _) (SimpPrimNormal _) = ?unify_missing_casee_25
  -- unify _ (RigidBinding _ _) (SimpObjCallable _) = ?unify_missing_casee_24
  -- unify _ (RigidBinding _ _) (MtaCallable _) = ?unify_missing_casee_23
  -- unify _ (MtaCallable _) (SimpObjCallable _) = ?unify_missing_casee_13
  -- unify _ (MtaCallable _) (RigidBinding _ _) = ?unify_missing_casee_14
  -- unify _ (MtaCallable _) (SimpPrimNormal _) = ?unify_missing_casee_15
  -- unify _ (SimpObjCallable _) (MtaCallable _) = ?unify_missing_casee_18
  -- unify _ (SimpObjCallable _) (RigidBinding _ _) = ?unify_missing_casee_19
  -- unify _ (SimpObjCallable _) (SimpPrimNormal _) = ?unify_missing_casee_20
  -- unify _ (SimpPrimNormal _) (MtaCallable _) = ?unify_missing_casee_28
  -- unify _ (SimpPrimNormal _) (SimpObjCallable _) = ?unify_missing_casee_29
  -- unify _ (SimpPrimNormal _) (RigidBinding _ _) = ?unify_missing_casee_30
