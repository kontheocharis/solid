-- Solving metavariables and associated helpers.
module Core.Metavariables

import Utils
import Decidable.Equality
import Data.Maybe
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

-- A partial renaming is a "strengthening" followed by a monomorphism, followed
-- by a weakening.
--
-- The strengthening can fail, which means some variables are "escaping".
namespace PRen
  -- Here we represent a partial renaming as a partial function from indices to
  -- indices.
  public export
  record PRen (ns : Ctx) (ms : Ctx) where
    constructor MkPRen
    dom : Size ns
    cod : Size ms
    contains : Idx ms -> Maybe (Idx ns)

  public export
  id : Size ns -> PRen ns ns
  id s = MkPRen s s (\i => Just i)

  public export
  removeAll : Size ns -> PRen [<] ns
  removeAll s = MkPRen SZ s (\i => Nothing)

  public export
  lift : PRen ns ms -> PRen (ns :< n) (ms :< n')
  lift (MkPRen dom cod contains) = MkPRen (SS dom) (SS cod) (\i => case i of
    IZ => Just IZ
    IS k => map IS (contains k))

-- Invert a renaming if possible (i.e. if it is linear).
--
-- This yields a partial renaming.
--
-- Note: a renaming is just a substitution containing only variables.
invertRen : Size ns -> Sub ns Idx ms -> Maybe (PRen ms ns)
invertRen sns [<] = Just (removeAll sns)
invertRen sns (xs :< x) = do
  MkPRen dom cod contains <- invertRen sns xs
  case contains x of
    Nothing => Nothing
    Just i => Just (MkPRen (SS dom) cod
      (\i' => case decEq i' x of
        Yes Refl => Just (firstIdx dom)
        No _ => map IS (contains i')))

-- An error while performing renaming on a term.
public export
data PRenError : Ctx -> Type where
  -- A variable does not appear in the strengthening
  Escapes : Lvl ms -> PRenError ms
  -- A meta is invalid, e.g. trying to create a cyclic solution.
  InvalidMeta : MetaVar -> PRenError ms

Weak PRenError where
  weak s (Escapes l) = Escapes (weak s l)
  weak s (InvalidMeta m) = InvalidMeta m

-- Whether a metavariable is allowed to appear in a term being renamed.
data MetaValidity : Type where
  Valid : MetaValidity
  Invalid : MetaValidity

differentFrom : MetaVar -> MetaVar -> MetaValidity
differentFrom m m' = case decEq m m' of
  Yes Refl => Invalid
  No _ => Valid

-- What is the plan? It consists of a partial renaming and a function that
-- decides whether a meta variable can appear here.
public export
record Plan (ns : Ctx) (ms : Ctx) (us : Ctx) where
  constructor MkPlan
  ren : PRen ns ms
  lifted : Size us -- how many times we lifted the renaming
  metaValidity : MetaVar -> MetaValidity

-- Lift the plan by a bound variable
--
-- Does not affect the renaming.
public export
lift : Plan ns ms us -> Plan ns ms (us :< u)
lift (MkPlan ren lifted v) = MkPlan ren (SS lifted) v

-- The renaming interface
public export
interface Rename (0 tm : Ctx -> Type) where
  rename : Plan ns ms us -> tm (ms ++ us) -> Either (PRenError ms) (tm (ns ++ us))

-- Should use this function for doing the actual renaming
public export
ren : Rename tm => PRen ns ms -> (MetaVar -> MetaValidity) -> tm ms -> Either (PRenError ms) (tm ns)
ren p m = rename (MkPlan p SZ m)

-- Renaming for the syntax:

renameLazy : Rename tm => Plan ns ms us -> Lazy (tm (ms ++ us)) -> Either (PRenError ms) (Lazy (tm (ns ++ us)))
renameLazy @{t} p gl = delay <$> rename @{t} p (force gl)

Rename (Term Syntax)

Rename (Spine ar (Term Syntax)) where
  rename p sp = traverseSpine (rename p) sp

Rename (PrimitiveApplied k Syntax e) where
  rename p (h $$ sp) = [| pure h $$ rename p sp |]

Rename (Binder md r Syntax n) where
  rename p b = traverseBinder (rename p) b

Rename Idx where
  -- We have not lifted; proceed with renaming
  rename (MkPlan pren SZ v) i = case pren.contains i of
    Just j => pure j
    Nothing => Left (Escapes (idxToLvl pren.cod i))

  -- We have lifted. Do not rename, just recurse
  rename (MkPlan pren (SS lifted) v) IZ = pure IZ
  rename (MkPlan pren (SS lifted) v) (IS i') = [| IS (rename (MkPlan pren lifted v) i') |]

Rename (Variable Syntax) where
  rename p (Index l) = [| Index (rename p l) |]

Rename (Body Syntax n) where
  rename p (Delayed t) = [| Delayed (rename (lift p) t) |]

Rename (Binding md r Syntax) where
  rename p (Bound md {n = n} bind body) = Bound md {n = n} <$> rename p bind <*> rename p body

Rename (Head Syntax NA) where
  rename p (SynVar v) = SynVar <$> rename p v
  rename p (SynMeta v) = case p.metaValidity v of
    Valid => pure (SynMeta v)
    Invalid => Left (InvalidMeta v)
  rename p (SynBinding md r t) = SynBinding md r <$> rename p t
  rename p (PrimNeutral prim) = PrimNeutral <$> rename p prim

Rename (HeadApplied Syntax NA) where
  rename p (($$) {ar = ar} h sp) = [| ($$) {ar = ar} (rename p h) (rename p sp) |]

public export
Rename (Term Syntax) where
  rename p (SynApps as) = [| SynApps (rename p as) |]
  rename p (RigidBinding md t) = RigidBinding md <$> rename p t
  rename p (SynPrimNormal prim) = [| SynPrimNormal (rename p prim) |]

-- Ensure that a spine contains all variables, and thus
-- turn it into a renaming.
--
-- This returns nothing if the spine contains a non-variable.
spineToRen : (resolve : Term Value ns -> Term Value ns)
  -> Size ns
  -> Spine ar (Term Value) ns
  -> Maybe (Sub ns Idx (arityToCtx ar))
spineToRen resolve s [] = Just [<]
spineToRen resolve s (x :: xs) = case resolve x of
  SimpApps (ValVar (Level l) $$ []) => do
    xs' <- spineToRen resolve s xs
    pure $ [<lvlToIdx s l] ++ xs'
  _ => Nothing

-- Actually solving metavariables

data SolveError : Ctx -> Type where
  -- A variable appears more than once in the metavariable spine.
  NonLinear : Spine ar (Term Value) ns -> SolveError ns
  -- The metavariable spine contains a non-variable entry
  NonVar : Spine ar (Term Value) ns -> SolveError ns
  -- A renaming error occurred while preparing the solution
  RenamingError : PRenError ns -> SolveError ns

Weak SolveError where
  weak s (NonLinear sp) = NonLinear (weak s sp)
  weak s (NonVar sp) = NonVar (weak s sp)
  weak s (RenamingError err) = RenamingError (weak s err)

-- A flex is a metavariable applied to a spine of arguments
data Flex : MetaVar -> Ctx -> Type where
  MkFlex : (m : MetaVar) -> (sp : Spine ar (Term Value) ns) -> Flex m ns

-- Solve a problem of the form
--
-- ?m sp =? t
solve : (resolve : Term Value ns -> Term Value ns)
  -> Size ns
  -> Flex m ns
  -> Term Value ns
  -> Either (SolveError ns) (Term Value [<])
solve resolve s (MkFlex m sp) t =
  -- Turn the spine into a renaming
  case spineToRen resolve s sp of
    Nothing => Left (NonVar sp)
    -- Invert to get a partial renaming
    Just sp' => case invertRen s sp' of
      Nothing => Left (NonLinear sp)
      Just pren =>
        -- Apply the partial renaming to the term, and wrap it in lambdas to
        -- close it
        let st : Term Syntax _ = quote s t in
        case ren pren (differentFrom m) st of
          Left err => Left (RenamingError err)
          Right t' => Right (eval {over = Term Value} [<] $ lams pren.dom t')
