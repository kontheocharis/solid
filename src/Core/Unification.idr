module Core.Unification

import Utils
import Core.Context
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

{r, r' : Reducibility} -> Unify (Thunk md r Value) (Thunk md r' Value) where
  unify s (Bound md n bindA bodyA) (Bound md n' bindB bodyB)
    = unify s bindA bindB /\ unify s bodyA bodyB

{hk : PrimitiveClass} -> Unify (PrimitiveApplied hk Value Simplified) (PrimitiveApplied hk Value Simplified) where
  unify s (SimpApplied {r = PrimIrreducible} p sp) (SimpApplied {r = PrimIrreducible} p' sp')
    = byProofOrDiff (primEq p p') /\ unify s sp sp'
  unify s (SimpApplied p sp) (SimpApplied p' sp')
    = byProofOrIdk (primEq p p') /\ unify s sp sp'

Unify (Head Value Simplified) (Head Value Simplified) where
  unify s (ValVar v) (ValVar v') = unify s v v'
  unify s (ValMeta m) (ValMeta m') = ?metasBro
  unify s (PrimNeutral p) (PrimNeutral p') = unify s p p'
  unify s _ _ = DontKnow

Unify (HeadApplied Value Simplified) (HeadApplied Value Simplified) where
  unify s (h $$ sp) (h' $$ sp') = unify s h h' /\ unify s sp sp'

Unify (Term Value) (Term Value) where
  unify s (SimpApps a) (SimpApps a') = unify s a a'

  unify _ (Glued _) (Glued _) = ?unify_missing_case_10
  unify _ (MtaCallable _) (MtaCallable _) = ?unify_missing_case_21
  unify _ (SimpObjCallable _) (SimpObjCallable _) = ?unify_missing_case_31
  unify _ (RigidThunk _) (RigidThunk _) = ?unify_missing_case_41

  unify s (SimpPrimNormal p) (SimpPrimNormal p') = unify s p p'

  unify _ (SimpApps _) (Glued _) = ?unify_missing_case_1
  unify _ (SimpApps _) (MtaCallable _) = ?unify_missing_case_2
  unify _ (SimpApps _) (SimpObjCallable _) = ?unify_missing_case_3
  unify _ (SimpApps _) (RigidThunk _) = ?unify_missing_case_4
  unify _ (SimpApps _) (SimpPrimNormal _) = ?unify_missing_case_5
  unify _ (Glued _) (SimpApps _) = ?unify_missing_case_60
  unify _ (Glued _) (MtaCallable _) = ?unify_missing_case_70
  unify _ (Glued _) (SimpObjCallable _) = ?unify_missing_case_80
  unify _ (Glued _) (RigidThunk _) = ?unify_missing_case_90
  unify _ (Glued _) (SimpPrimNormal _) = ?unify_missing_casee_10
  unify _ (MtaCallable _) (Glued _) = ?unify_missing_casee_11
  unify _ (MtaCallable _) (SimpApps _) = ?unify_missing_casee_12
  unify _ (MtaCallable _) (SimpObjCallable _) = ?unify_missing_casee_13
  unify _ (MtaCallable _) (RigidThunk _) = ?unify_missing_casee_14
  unify _ (MtaCallable _) (SimpPrimNormal _) = ?unify_missing_casee_15
  unify _ (SimpObjCallable _) (Glued _) = ?unify_missing_casee_16
  unify _ (SimpObjCallable _) (SimpApps _) = ?unify_missing_casee_17
  unify _ (SimpObjCallable _) (MtaCallable _) = ?unify_missing_casee_18
  unify _ (SimpObjCallable _) (RigidThunk _) = ?unify_missing_casee_19
  unify _ (SimpObjCallable _) (SimpPrimNormal _) = ?unify_missing_casee_20
  unify _ (RigidThunk _) (Glued _) = ?unify_missing_casee_21
  unify _ (RigidThunk _) (SimpApps _) = ?unify_missing_casee_22
  unify _ (RigidThunk _) (MtaCallable _) = ?unify_missing_casee_23
  unify _ (RigidThunk _) (SimpObjCallable _) = ?unify_missing_casee_24
  unify _ (RigidThunk _) (SimpPrimNormal _) = ?unify_missing_casee_25
  unify _ (SimpPrimNormal _) (Glued _) = ?unify_missing_casee_26
  unify _ (SimpPrimNormal _) (SimpApps _) = ?unify_missing_casee_27
  unify _ (SimpPrimNormal _) (MtaCallable _) = ?unify_missing_casee_28
  unify _ (SimpPrimNormal _) (SimpObjCallable _) = ?unify_missing_casee_29
  unify _ (SimpPrimNormal _) (RigidThunk _) = ?unify_missing_casee_30

  -- never happens
