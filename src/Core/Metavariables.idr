-- Solving metavariables and associated helpers.
module Core.Metavariables

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
  id : Size ns -> PRen ns ns
  id SZ = Terminal
  id (SS k) = Retain (id k . Drop Id) LZ

  public export
  removeAll : Size ns -> PRen [<] ns
  removeAll SZ = Terminal
  removeAll (SS k) = Remove (removeAll k)

  public export
  contains : Lvl ns -> PRen ns ms -> Bool
  contains l Terminal = False
  contains l (Retain p l') = case decEq l l' of
    Yes Refl => True
    No _ => contains l p
  contains l (Remove p) = contains l p

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

-- Lift the plan by a bound variable
--
-- Does not affect the renaming.
public export
lift : Plan ns ms us -> Plan ns ms (us :< u)
lift (MkPlan dom cod ren lifted v) = MkPlan dom cod ren (SS lifted) v

-- The renaming interface
public export
interface Rename (0 tm : Ctx -> Type) where
  rename : Plan ns ms us -> tm (ms ++ us) -> Either (PRenError ms) (tm (ns ++ us))

-- Should use this function for doing the actual renaming
public export
ren : Rename tm => Size ns -> PRen ns ms -> (MetaVar -> Bool) -> tm ms -> Either (PRenError ms) (tm ns)
ren dom p metaIsValid = rename (MkPlan dom p.size p SZ metaIsValid)

-- Renaming for the syntax:

renameLazy : Rename tm => Plan ns ms us -> Lazy (tm (ms ++ us)) -> Either (PRenError ms) (Lazy (tm (ns ++ us)))
renameLazy @{t} p gl = delay <$> rename @{t} p (force gl)

Rename (Term Syntax)

Rename (Spine ar (Term Syntax)) where
  rename p sp = traverseSpine (rename p) sp

Rename (PrimitiveApplied k Syntax e) where
  rename p (h $$ sp) = [| pure h $$ rename p sp |]

Rename (Binder md r Syntax) where
  rename p b = traverseBinder (rename p) b

Rename Idx where
  -- We have not lifted; proceed with renaming
  rename (MkPlan dom (SS cod) (Retain p l) SZ v) IZ = pure (lvlToIdx dom l)
  -- Found an escaping variable! it is currently the first index so the last level
  rename (MkPlan dom (SS cod) (Remove p) SZ v) IZ = Left (Escapes (lastLvl cod))
  rename (MkPlan dom (SS cod) (Retain p l) SZ v) (IS i') = mapFst wk (rename (MkPlan dom cod p SZ v) i')
  rename (MkPlan dom (SS cod) (Remove p) SZ v) (IS i') = mapFst wk (rename (MkPlan dom cod p SZ v) i')

  -- We have lifted. Do not rename, just recurse
  rename (MkPlan dom cod p (SS lifted) v) IZ = pure IZ
  rename (MkPlan dom cod p (SS lifted) v) (IS i') = [| IS (rename (MkPlan dom cod p lifted v) i') |]

Rename (Variable Syntax) where
  rename p (Index l) = [| Index (rename p l) |]

Rename (Body Syntax n) where
  rename p (Delayed t) = [| Delayed (rename (lift p) t) |]

Rename (Binding md r Syntax) where
  rename p (Bound md n bind body) = Bound md n <$> rename p bind <*> rename p body

Rename (Head Syntax NA) where
  rename p (SynVar v) = SynVar <$> rename p v
  rename p (SynMeta v) = if p.metaIsValid v then pure (SynMeta v) else Left (InvalidMeta v)
  rename p (SynBinding md r t) = SynBinding md r <$> rename p t
  rename p (PrimNeutral prim) = PrimNeutral <$> rename p prim

Rename (HeadApplied Syntax NA) where
  rename p (($$) {ar = ar} h sp) = [| ($$) {ar = ar} (rename p h) (rename p sp) |]

public export
Rename (Term Syntax) where
  rename p (SynApps as) = [| SynApps (rename p as) |]
  rename p (RigidBinding md t) = RigidBinding md <$> rename p t
  rename p (SynPrimNormal prim) = [| SynPrimNormal (rename p prim) |]

-- Spine inversion

data InvertError : Ctx -> Type where
  -- The given variable appears more than once in the spine
  NonLinear : Lvl ns -> InvertError ns
  -- The spine contains the given non-variable entry
  NonVar : Term Value ns -> InvertError ns

Weak InvertError where
  weak s (NonLinear l) = NonLinear (weak s l)
  weak s (NonVar t) = NonVar (weak s t)

-- 0 Ren' : Ctx -> Ctx -> Type
-- Ren' ns ms = List (Lvl ns, Lvl ms)
--

lookup : Sub ns Lvl ms -> Lvl ns -> Maybe (Lvl ms)

invert : Size ns -> Sub ns Lvl ms -> Either (InvertError ns) (PRen ms ns)
invert SZ sp = pure Terminal
invert (SS s) sp = case lookup sp (lastLvl s) of
  Just l => ?fafaa
  Nothing => pure (Remove ?fafa)

  -- return ()

-- invert
-- invert SZ sp = pure Terminal
-- invert (SS u) (sp :< x) = Right (Retain (?ff) x)
-- invert s [<] = pure (removeAll s)
-- invert s@(SS _) (xs :< x) = do
--   pren <- invert s xs
--   let x' = ?x
--   if contains x' pren
--     then Left (NonLinear x)
--     else Right ?ff

-- invert (SS s) sp = do
--   l <- mapFst wk (invert s ?sp)
--   pure (Retain l ?ff)

-- Retain <$> (?o) <*> pure ?ff

-- Actually solving metavariables

data Flex : MetaVar -> Ctx -> Type where
  MkFlex : (m : MetaVar) -> (sp : Spine ar (Term Value) ns) -> Flex m ns

solve : Size ns -> Flex m ns -> Term Value ns -> Unification
solve s fl = ?solveMeta_rhs

intersect : Size ns -> Flex m ns -> Flex m ns -> Unification
intersect s fl fl' = ?intersect_rhs

merge : Size ns -> Flex m ns -> Flex m' ns -> Unification
merge s fl fl' = ?join_rhs
