-- General context utilities, precursor to typechecking
module Core.Context

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Data.Maybe
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Metavariables
import Core.Unification
import Core.Atoms

%default covering

-- Context for typechecking
public export
record Context (ns : Ctx) where
  constructor MkContext
  -- All the identifiers in scope
  idents : Singleton ns
  -- The current context of types
  con : Con AtomTy ns
  -- The current context of sorts
  sorts : Con AtomTy ns
  -- The definitions in the context
  --
  -- This is an endomorphism of `con`; bindings are mapped to their level, and
  -- definitions are mapped to their value.
  defs : Sub ns Atom ns
  -- The stages of the definitions in the context
  stages : Con (const Stage) ns
  -- The size of the context, for quick access
  size : Size ns
  -- The bound variables in the context, in the form of a spine ready to be applied
  -- to a metavariable.
  binds : Exists (\ar => Spine ar AtomTy ns)
  
public export
emptyContext : Context [<]
emptyContext =
  MkContext (Val [<]) [<] [<] [<] [<] SZ (Evidence [] [])
 
-- A goal is a hole in a context.
public export
record Goal where
  constructor MkGoal
  {0 conNs : Ctx}

  -- The name of the goal hole, if given
  name : Maybe Name

  -- The actual hole term and its type
  hole : Expr conNs

  -- The context in which the goal exists
  ctx : Context conNs
  
public export
%hint
ctxSize : Context ns -> Size ns
ctxSize = .size

-- Find a name in the context
public export
lookup : Context ns -> Name -> Maybe (Idx ns)
lookup ctx n = findIdx ctx.idents n
  where
    findIdx : forall ns . Singleton ns -> Name -> Maybe (Idx ns)
    findIdx (Val [<]) n = Nothing
    findIdx (Val (ns :< (m, n'))) n = case n == n' of
      True => Just IZ
      False => do
        idx <- findIdx (Val ns) n
        pure $ IS idx

-- Add a potentially self-referencing definition to the context.
public export
addToContext : {s : Stage} -> (isBound : Bool) -> (n : Ident) -> AnnotAt s ns -> Atom (ns :< n) -> Context ns -> Context (ns :< n)
addToContext {s = stage}
  isBound n
  (MkAnnotAt ty sort)
  tm
  (MkContext (Val idents)
  con sorts defs stages size
  (Evidence ar bounds)) =
  MkContext
    (Val (idents :< n)) (con :< ty) (sorts :< sort) (defs `o` Drop Id :< tm) (stages :< stage) (SS size)
    (if isBound then (Evidence (ar ++ [n]) $ wkS bounds ++ [(Val _, tm)]) else (Evidence ar $ wkS bounds))

-- Add a definition to the context that lazily evaluates to its value.
public export
define : {s : Stage} -> (n : Ident) -> ExprAt s ns -> Context ns -> Context (ns :< n)
define n rhs ctx =
  addToContext False n rhs.annot (promote $ Glued (LazyApps (ValDef (Level here) $$ []) (wk rhs.tm.val))) ctx

-- Add a binding with no value to the context.
public export
bind : {s : Stage} -> (n : Ident) -> AnnotAt s ns -> Context ns -> Context (ns :< n)
bind n annot ctx = addToContext True n annot here ctx