-- (Parital) renaming and other transformations on syntax, used for solving metavariables.
module Core.Renaming

import Utils
import Decidable.Equality
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

-- A partial renaming is a "strengthening" followed by a monomorphism, followed
-- by a weakening.
--
-- The strengthening can fail, which means some variables are "escaping".
namespace PRen
  public export
  data PRen : Ctx -> Ctx -> Type where
    Terminal : PRen ns [<]
    Retain : PRen ns ms -> Lvl ns -> PRen ns (ms :< n)
    Remove : PRen ns ms -> PRen ns (ms :< n)

  public export
  (.size) : PRen ns ms -> Size ms
  (.size) Terminal = SZ
  (.size) (Retain p l) = SS p.size
  (.size) (Remove p) = SS p.size

  -- Closed under post-composition with weakenings
  public export
  (.) : PRen ms qs -> Wk ns ms -> PRen ns qs
  Terminal . e = Terminal
  Retain p l . e = Retain (p . e) (weak e l)
  Remove p . e = Remove (p . e)

  public export
  lift : Size ns -> PRen ns ms -> PRen (ns :< n) (ms :< n')
  lift s p = Retain (p . Drop Id) (here s)

public export
data PRenError : Ctx -> Type where
  -- A variable does not appear in the strengthening
  Escapes : Lvl ms -> PRenError ms
  -- A meta is invalid, e.g. trying to create a cyclic solution.
  InvalidMeta : MetaVar -> PRenError ms

Weak PRenError where
  weak s (Escapes l) = Escapes (weak s l)
  weak s (InvalidMeta m) = InvalidMeta m

-- What is the plan? It consists of a partial renaming and a function that
-- decides whether a meta variable can appear here.
public export
record Plan (ns : Ctx) (ms : Ctx) (us : Ctx) where
  constructor MkPlan
  dom : Size ns
  cod : Size ms
  ren : PRen ns ms
  lifted : Size us -- how many times we lifted the renaming
  metaIsValid : MetaVar -> Bool

public export
lift : Plan ns ms us -> Plan ns ms (us :< u)
lift (MkPlan dom cod ren lifted v) = MkPlan dom cod ren (SS lifted) v

public export
interface Rename (0 tm : Ctx -> Type) where
  rename : Plan ns ms us -> tm (ms ++ us) -> Either (PRenError ms) (tm (ns ++ us))

renameLazy : Rename tm => Plan ns ms us -> Lazy (tm (ms ++ us)) -> Either (PRenError ms) (Lazy (tm (ns ++ us)))
renameLazy @{t} p gl = delay <$> rename @{t} p (force gl)

Rename (Term Syntax)

Rename (Spine ar (Term Syntax)) where
  rename p sp = traverseSpine (rename p) sp

Rename (PrimitiveApplied k Syntax e) where
  rename p (h $$ sp) = [| pure h $$ rename p sp |]

public export
Rename (Binder md r Syntax) where
  rename p b = traverseBinder (rename p) b

public export
Rename Idx where
  -- We have not lifted; proceed with renaming
  rename (MkPlan dom (SS cod) (Retain p l) SZ v) IZ = pure (lvlToIdx dom l)
  rename (MkPlan dom (SS cod) (Remove p) SZ v) IZ = Left (Escapes (lastLvl cod))
  rename (MkPlan dom (SS cod) (Retain p l) SZ v) (IS i') = mapFst wk (rename (MkPlan dom cod p SZ v) i')
  rename (MkPlan dom (SS cod) (Remove p) SZ v) (IS i') = mapFst wk (rename (MkPlan dom cod p SZ v) i')

  -- We have lifted. Do not rename, just recurse
  rename (MkPlan dom cod p (SS lifted) v) IZ = pure IZ
  rename (MkPlan dom cod p (SS lifted) v) (IS i') = [| IS (rename (MkPlan dom cod p lifted v) i') |]

public export
Rename (Variable Syntax) where
  rename p (Index l) = [| Index (rename p l) |]

public export
Rename (Body Syntax n) where
  rename p (Delayed t) = [| Delayed (rename (lift p) t) |]

public export
Rename (Binding md r Syntax) where
  rename p (Bound md n bind body) = Bound md n <$> rename p bind <*> rename p body

public export
  Rename (Head Syntax NA) where
    rename p (SynVar v) = SynVar <$> rename p v
    rename p (SynMeta v) = if p.metaIsValid v then pure (SynMeta v) else Left (InvalidMeta v)
    rename p (SynBinding md r t) = SynBinding md r <$> rename p t
    rename p (PrimNeutral prim) = PrimNeutral <$> rename p prim

public export
Rename (HeadApplied Syntax NA) where
  rename p (($$) {ar = ar} h sp) = [| ($$) {ar = ar} (rename p h) (rename p sp) |]

public export
Rename (Term Syntax) where
  rename p (SynApps as) = [| SynApps (rename p as) |]
  rename p (RigidBinding md t) = RigidBinding md <$> rename p t
  rename p (SynPrimNormal prim) = [| SynPrimNormal (rename p prim) |]
