module Core.Renaming

import Utils
import Decidable.Equality
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

-- A partial renaming is a "strengthening" followed by an epimorphism, followed
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
  -- A meta is invalid, basically trying to create a cyclic solution.
  InvalidMeta : MetaVar -> PRenError ms

Weak PRenError where
  weak s (Escapes l) = Escapes (weak s l)
  weak s (InvalidMeta m) = InvalidMeta m

-- What is the plan? It consists of a partial renaming and a function that
-- decides whether a meta variable can appear here.
public export
record Plan (ns : Ctx) (ms : Ctx) where
  constructor MkPlan
  dom : Size ns
  cod : Size ms
  ren : PRen ns ms
  metaIsValid : MetaVar -> Bool

public export
interface Rename (0 src : Ctx -> Type) (0 dest : Ctx -> Type) where
  rename : Plan ns ms -> src ms -> Either (PRenError ms) (dest ns)

renameLazy : Rename src dest => Plan ns ms -> Lazy (src ms) -> Either (PRenError ms) (Lazy (dest ns))
renameLazy @{t} p gl = delay <$> rename @{t} p (force gl)

Rename (Term Value) (Term Value)

Rename (Spine ar (Term Value)) (Spine ar (Term Value)) where
  rename p [] = pure []
  rename p (x :: xs) = [| rename p x :: rename p xs |]

Rename (PrimitiveApplied k Value e) (PrimitiveApplied k Value e) where
  rename p (SimpApplied h sp) = [| SimpApplied (pure h) (rename p sp) |]
  rename p (LazyApplied h sp gl) = [| LazyApplied (pure h) (rename p sp) (renameLazy p gl) |]

public export
Rename (Binder md r Value) (Binder md r Value) where
  rename p b = traverseBinder (rename p) b

-- We do the renaming on indices, because renaming is index-based.
public export
Rename Idx Lvl where
  rename (MkPlan dom (SS cod) (Retain p l) v) IZ = pure l
  rename (MkPlan dom (SS cod) (Remove p) v) IZ = Left (Escapes (lastLvl cod))
  rename (MkPlan dom (SS cod) (Retain p l) v) (IS i') = mapFst wk (rename (MkPlan dom cod p v) i')
  rename (MkPlan dom (SS cod) (Remove p) v) (IS i') = mapFst wk (rename (MkPlan dom cod p v) i')

public export
Rename Lvl Lvl where
  rename p l = rename p (lvlToIdx p.cod l)
