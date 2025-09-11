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
record Context (bs : Ctx) (ns : Ctx) where
  --            ^ bindings  ^ bindings + lets
  constructor MkContext
  -- All the identifiers in scope
  idents : Singleton ns
  -- The current context (types)
  con : Con AtomTy ns
  -- The current context (sorts)
  sorts : Con AtomTy ns
  -- The definitions in the context
  defs : Sub bs Atom ns
  -- Bindings are OPEd into definitions
  undefs : Th ns bs
  -- The stages of the definitions in the context
  stages : Con (const Stage) ns
  -- The size of the bindings, for quick access
  sizeBinds : Size bs
  -- The size of the context, for quick access
  sizeNames : Size ns
  -- The bound variables in the context, in the form of a spine ready to be applied
  -- to a metavariable.
  binds : Spine (ctxToArity bs) AtomTy bs
  
public export
emptyContext : Context [<] [<]
emptyContext =
  MkContext (Val [<]) [<] [<] [<] Done [<] SZ SZ []
 
-- A goal is a hole in a context.
public export
record Goal where
  constructor MkGoal
  {0 bindNs : Ctx}
  {0 conNs : Ctx}

  -- The name of the goal hole, if given
  name : Maybe Name

  -- The actual hole term and its type
  hole : Expr conNs

  -- The context in which the goal exists
  ctx : Context bindNs conNs
  
public export
%hint
ctxSize : Context bs ns -> Size ns
ctxSize = .sizeNames
  
public export
%hint
bindsSize : Context bs ns -> Size bs
bindsSize = .sizeBinds

-- Find a name in the context
public export
lookup : Context bs ns -> Name -> Maybe (Idx ns)
lookup ctx n = findIdx ctx.idents n
  where
    findIdx : forall ns . Singleton ns -> Name -> Maybe (Idx ns)
    findIdx (Val [<]) n = Nothing
    findIdx (Val (ns :< (m, n'))) n = case n == n' of
      True => Just IZ
      False => do
        idx <- findIdx (Val ns) n
        pure $ IS idx

-- Add a binding with no value to the context.
public export
bind : {s : Stage} -> (n : Ident) -> AnnotAt s ns -> Context bs ns -> Context (bs :< n) (ns :< n)
bind {s = stage}
  n
  (MkAnnotAt ty sort)
  (MkContext (Val idents) con sorts defs undefs stages sizeBinds sizeNames bounds) =
  MkContext
    (Val (idents :< n)) (con :< ty) (sorts :< sort)
      (defs `o` Drop Id :< here)
    (Keep undefs) (stages :< stage) (SS sizeBinds) (SS sizeNames) 
    (wkS bounds ++ [(Val _, here)])

-- Add a definition to the context.
public export
define : {s : Stage} -> (n : Ident) -> AnnotAt s ns -> Atom ns -> Context bs ns -> Context bs (ns :< n)
define {s = stage}
  n
  (MkAnnotAt ty sort)
  tm
  (MkContext (Val idents) con sorts defs undefs stages sizeBinds sizeNames bounds) =
  MkContext
    (Val (idents :< n)) (con :< ty) (sorts :< sort)
      (defs :< sub defs tm)
    (Drop undefs) (stages :< stage) sizeBinds (SS sizeNames)
    bounds