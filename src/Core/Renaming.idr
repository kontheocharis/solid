module Core.Renaming

import Utils
import Decidable.Equality
import Core.Base
import Core.Syntax
import Core.Evaluation

%default covering

-- A partial renaming is a "strengthening" followed by an isomorphism
--
-- The strengthening can fail, which means some variables are "escaping".
namespace PRen
  public export
  data PRen : Ctx -> Ctx -> Type where
    Terminal : PRen ns [<]
    Keep : PRen ns ms -> Lvl ns -> PRen ns (ms :< n)
    Drop : PRen ns ms -> PRen ns (ms :< n)

  -- Closed under post-composition with weakenings
  (.) : PRen ms qs -> Wk ns ms -> PRen ns qs
  Terminal . e = Terminal
  Keep p l . e = Keep (p . e) (weak e l)
  Drop p . e = Drop (p . e)

  lift : Size ns -> PRen ns ms -> PRen (ns :< n) (ms :< n')
  lift s p = Keep (p . Drop Id) (here s)

public export
data PRenError : Ctx -> Ctx -> Type where
  -- A variable does not appear in the strengthening
  Escapes : Lvl ms -> PRenError ns ms
  -- A meta is invalid, basically trying to create a cyclic solution.
  InvalidMeta : MetaVar -> PRenError ns ms

-- What is the plan? It consists of a partial renaming and a function that
-- decides whether a meta variable can appear here.
public export
record Plan (ns : Ctx) (ms : Ctx) where
  ren : PRen ns ms
  metaIsValid : MetaVar -> Bool

public export
interface Rename (0 tm : Ctx -> Type) (0 ns : Ctx) (0 ms : Ctx) where
  rename : Size ns -> Plan ns ms -> tm ms -> Either (PRenError ns ms) (tm ns)
