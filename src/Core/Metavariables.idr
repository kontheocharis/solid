-- Solving metavariables and associated helpers.
module Core.Metavariables

import Utils
import Common
import Decidable.Equality
import Data.Maybe
import Data.Singleton
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Atoms

%default covering

-- A renaming is just a substitution containing only variables. A partial
-- renaming is a renaming that leaves gaps for some variables in the output
-- context.
--
-- A partial renaming can be viewed a "strengthening" followed by a monomorphism
-- (using each variable at least once), followed by a weakening. The
-- strengthening can fail, which means some variables are "escaping".
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
  id : Size ns => PRen ns ns
  id @{s} = MkPRen s s (\i => Just i)

  public export
  removeAll : Size ns => PRen [<] ns
  removeAll @{s} = MkPRen SZ s (\i => Nothing)

  public export
  lift : PRen ns ms -> PRen (ns :< n) (ms :< n')
  lift (MkPRen dom cod contains) = MkPRen (SS dom) (SS cod) (\i => case i of
    IZ => Just IZ
    IS k => map IS (contains k))

-- Invert a renaming if possible (if it is an epimorphism, i.e. if it is linear).
--
-- This yields a partial renaming.
invertRen : Size ns => Sub ns Idx ms -> Maybe (PRen ms ns)
invertRen [<] = Just removeAll
invertRen (xs :< x) = do
  MkPRen dom cod contains <- invertRen xs
  case contains x of
    Just _ => Nothing
    Nothing => Just (MkPRen (SS dom) cod
      (\i' => case decEq i' x of
        Yes Refl => Just IZ
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

Thin PRenError where
  thin s (Escapes l) = Escapes (thin s l)
  thin s (InvalidMeta m) = InvalidMeta m
  
Relabel PRenError where
  relabel s (Escapes l) = Escapes (relabel s l)
  relabel s (InvalidMeta m) = InvalidMeta m
  
(ns : Ctx) => Show (PRenError ns) where
  show (Escapes x) = "variable `\{show x}` escapes meta solution"
  show (InvalidMeta x) = "cyclic or invalid metavariable `\{show x}` occurrence"

-- Whether a metavariable is allowed to appear in a term being renamed.
data MetaValidity : Type where
  Valid : MetaValidity
  Invalid : MetaValidity

differentFrom : MetaVar -> MetaVar -> MetaValidity
differentFrom m m' = case decEq m m' of
  Yes Refl => Invalid
  No _ => Valid

-- This consists of a partial renaming and a function that
-- decides whether a meta variable can appear here.
--
-- @@Todo: add spine pruning support to this.
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

-- Actually solving metavariables

-- Whether we are allowed to solve metavariables in a given context.
public export
data SolvingMode : Type where
  SolvingAllowed : SolvingMode
  SolvingNotAllowed : SolvingMode

-- A monad for metavariable solving.
public export
interface (forall sm . Monad (m sm)) => HasMetas (0 m : SolvingMode -> Type -> Type) where
  -- Get the solution of a metavariable, if any.
  getMeta : MetaVar -> m sm (Maybe (Term Value [<]))

  -- Create a new metavariable without a solution.
  newMeta : Maybe Name -> m sm MetaVar

  -- Check if we are allowed to solve metavariables.
  canSolve : m sm (Singleton sm)

  -- Solve a metavariable.
  setSolution : MetaVar -> Term Value [<] -> m SolvingAllowed ()

  -- Switch to a context where we are not allowed to solve metavariables.
  noSolving : {sm : SolvingMode} -> m SolvingNotAllowed a -> m sm a

  -- Get all metas
  getAllMetas : m sm Metas

public export
data SolveError : Ctx -> Type where
  -- A variable appears more than once in the metavariable spine.
  NonLinear : Spine ar (Term Value) ns -> SolveError ns
  -- The metavariable spine contains a non-variable entry
  NonVar : Spine ar (Term Value) ns -> SolveError ns
  -- A renaming error occurred while preparing the solution
  RenamingError : PRenError ns -> SolveError ns

public export
Weak SolveError where
  weak s (NonLinear sp) = NonLinear (weak s sp)
  weak s (NonVar sp) = NonVar (weak s sp)
  weak s (RenamingError err) = RenamingError (weak s err)

public export
Thin SolveError where
  thin s (NonLinear sp) = NonLinear (thin s sp)
  thin s (NonVar sp) = NonVar (thin s sp)
  thin s (RenamingError err) = RenamingError (thin s err)

public export
Relabel SolveError where
  relabel s (NonLinear sp) = NonLinear (relabel s sp)
  relabel s (NonVar sp) = NonVar (relabel s sp)
  relabel s (RenamingError err) = RenamingError (relabel s err)
  
export
(ns : Ctx) => ShowSyntax => Show (SolveError ns) where
    show (NonLinear sp) = "metavariable is applied to a non-linear spine: `\{show sp}`"
    show (NonVar sp) = "metavariable is applied to non-variable terms: `\{show sp}`"
    show (RenamingError err) = "renaming error occurred while solving metavariable: `\{show err}`"

-- A flex is a metavariable applied to a spine of arguments
public export
data Flex : MetaVar -> Ctx -> Type where
  MkFlex : (meta : MetaVar) -> (sp : Spine ar (Term Value) ns) -> Flex meta ns

(.meta) : Flex meta ns -> MetaVar
(.meta) (MkFlex m _) = m

-- Resolve any top-level metas appearing in the value
export
metaResolver : HasMetas m => Resolver (m sm) (Val ns)
metaResolver = repeatedly $ \case
  SimpApps (ValMeta m $$ sp) => getMeta m >>= \case
    Nothing => pure Nothing
    Just t' => pure $ Just (apps (weak Terminal t') sp)
  _ => pure Nothing
  
export
glueAndMetaResolver : HasMetas m => Resolver (m sm) (Val ns)
glueAndMetaResolver = glueResolver <+> metaResolver
  
-- Ensure that a spine contains all variables, and thus
-- turn it into a renaming.
--
-- This returns nothing if the spine contains a non-variable.
spineToRen : (HasMetas m) => (sz : Size ns)
  => Spine ar (Term Value) ns
  -> m sm (Maybe (Sub ns Idx (arityToCtx ar)))
spineToRen [] = pure $ Just [<]
spineToRen {sz = s} ((_, x) :: xs) = resolve glueAndMetaResolver x >>= \case
  SimpApps (ValVar (Level l) $$ []) => do
    xs' <- spineToRen xs
    pure $ ([<lvlToIdx s l] ++) <$> xs'
  _ => pure Nothing

-- Create the solution to a problem of the form
--
-- ?m sp =? t
solution : (HasMetas m) => Size ns
  => Flex meta ns
  -> Term Value ns
  -> m sm (Either (SolveError ns) (Term Value [<]))
solution (MkFlex m sp) t =
  -- Turn the spine into a renaming
  spineToRen sp >>= \case
    Nothing => pure $ Left (NonVar sp)
    -- Invert to get a partial renaming
    Just sp' => case invertRen sp' of
      Nothing => pure $ Left (NonLinear sp)
      Just pren =>
        -- Apply the partial renaming to the term, and wrap it in lambdas to
        -- close it
        let st : Term Syntax _ = quote t in
        case ren pren (differentFrom m) st of
          Left err => pure $ Left (RenamingError err)
          Right t' => pure $ Right (eval {over = Term Value} [<] $ closeWithLams pren.dom t')

-- Solve a problem and store it in the metavariable context
public export
solveProblem : (HasMetas m) => Size ns
  => Flex meta ns
  -> Term Value ns
  -> m SolvingAllowed (Either (SolveError ns) ())
solveProblem fl t = solution fl t >>= \case
  Left err => pure $ Left err
  Right t' => Right <$> setSolution fl.meta t'
