module Context

%default total

-- A bound variable is either from an explicit or an implicit pi.
--
-- We remember this in the context.
public export
data PiMode = Explicit | Implicit

-- A name is a member of a 'context skeleton'
public export
0 Name : Type
Name = (PiMode, String)

-- A context skeleton.
--
-- This will usually be marked computationally irrelevant.
-- Used to make syntax well-scoped.
public export
0 Ctx : Type
Ctx = SnocList Name

-- An arity is a context skeleton linked forward instead of backward.
--
-- This is to avoid green slime like [< x] ++ xs in later definitions.
public export
0 Arity : Type
Arity = List Name

export infixl 7 ::<

-- Extend a context skeleton with some arity.
public export
(::<) : Ctx -> Arity -> Ctx
ns ::< [] = ns
ns ::< (a :: as) = (ns :< a) ::< as

-- De-Brujin indices
public export
data Idx : Ctx -> Type where
  IZ : Idx (ns :< n)
  IS : Idx ns -> Idx (ns :< n)

-- De-Brujin levels.
--
-- Careful! LZ does not index the name n!
-- Rather the first element of (ns :< n).
public export
data Lvl : Ctx -> Type where
  LZ : Lvl (ns :< n)
  LS : Lvl ns -> Lvl (ns :< n)

-- Remember only the size of a context skeleton.
public export
data Size : Ctx -> Type where
  SZ : Size [<]
  SS : Size ns -> Size (ns :< n)

-- Some de-Brujin helpers:

public export
firstIdx : Size ns -> Idx (ns :< n)
firstIdx SZ = IZ
firstIdx (SS n) = IS (firstIdx n)

public export
nextIdx : Idx ns -> Idx (ns :< n)
nextIdx IZ = IZ
nextIdx (IS i) = IS (nextIdx i)

public export
lvlToIdx : Size ns -> Lvl ns -> Idx ns
lvlToIdx (SS n) LZ = firstIdx n
lvlToIdx (SS n) (LS l) = nextIdx (lvlToIdx n l)

public export
lastLvl : Size ns -> Lvl (ns :< n)
lastLvl SZ = LZ
lastLvl (SS n) = LS (lastLvl n)

-- Telescopes, spines, contexts and substitutions parameterised over
-- the actual syntax they contain

namespace Tel
  public export
  data Tel : Arity -> (Ctx -> Type) -> Ctx -> Type where
    Nil : Tel [] f ms
    (::) : f ms -> Tel as f (ms :< a) -> Tel (a :: as) f ms

namespace Spine
  public export
  data Spine : Arity -> (Ctx -> Type) -> Ctx -> Type where
    Nil : Spine [] f ns
    (::) : f ns -> Spine as f ns -> Spine (a :: as) f ns

  public export
  (++) : Spine as f ns -> Spine bs f ns -> Spine (as ++ bs) f ns
  [] ++ sp' = sp'
  (x :: sp) ++ sp' = x :: (sp ++ sp')

namespace Con
  data Con : (Ctx -> Type) -> Ctx -> Type where
    Lin : Con f [<]
    (:<) : Con f as -> f as -> Con f (as :< a)

namespace Sub
  public export
  data Sub : Ctx -> (Ctx -> Type) -> Ctx -> Type where
    Lin : Sub ns f [<]
    (:<) : Sub ns f ms -> f ns -> Sub ns f (ms :< m)

-- Order-preserving embeddings, AKA thinnings
namespace OPE
  public export
  data OPE : Ctx -> Ctx -> Type where
    Lin : OPE [<] [<]
    Id : OPE ns ns -- explicit identity to make `wk` easier to implement
    Keep : OPE ns ms -> OPE (ns :< n) (ms :< n)
    Drop : OPE ns ms -> OPE (ns :< n) ms

-- Some interfaces for syntax that involves variables

-- Weakening
public export
interface Thin (0 tm : Ctx -> Type) where
  thin : OPE ns ms -> tm ms -> tm ns

public export
(.) : Thin tm => Sub ms tm qs -> OPE ns ms -> Sub ns tm qs
[<] . e = [<]
(xs :< x) . e = xs . e :< thin e x

public export
wk : Thin tm => tm ns -> tm (ns :< n)
wk x = thin (Drop Id) x

-- Syntax supports variables if it supports thinnings and the zero-th deBrujin
-- index.
public export
interface (Thin tm) => Vars (0 tm : Ctx -> Type) where
  here : Size ns -> tm (ns :< n)

public export
lift : (Thin tm, Vars tm) => Size ns -> Sub ns tm ms -> Sub (ns :< a) tm (ms :< a)
lift s env = env . Drop Id :< here s

public export
id : (Thin tm, Vars tm) => Size ns -> Sub ns tm ns
id SZ = [<]
id (SS k) = lift k (id k)

public export
proj : (Thin tm, Vars tm) => Size ns -> Sub (ns :< n) tm ns
proj s = id s . Drop Id

-- Evaluation and quoting interfaces

public export
interface Eval (0 over : Ctx -> Type) (0 tm : Ctx -> Type) (0 val : Ctx -> Type) where
  eval : Sub ns over ms -> tm ms -> val ns

public export
interface Quote (0 val : Ctx -> Type) (0 tm : Ctx -> Type) where
  quote : Size ns -> val ns -> tm ns

-- Basic implementations for the defined types

public export
Thin Lvl where

  -- @@Todo: use %transform, do not rely on identity optimisation
  thin (Keep x) LZ = LZ
  thin (Keep x) (LS l) = LS (thin x l)
  thin (Drop x) LZ = LZ
  thin (Drop x) (LS l) = LS (thin x (wkLvl l))
    where
      wkLvl : Lvl us -> Lvl (us :< u)
      wkLvl LZ = LZ
      wkLvl (LS l) = LS (wkLvl l)
  thin Id l = l

public export
Thin Idx where
  -- wk = IS

  thin (Keep x) IZ = IZ
  thin (Keep x) (IS i) = IS (thin x i)
  thin (Drop x) i = IS (thin x i) -- here is the non-free bit for indices!
  thin Id i = i

public export
(Thin tm) => Thin (Spine as tm) where
  thin e [] = []
  thin e (x :: xs) = thin e x :: thin e xs

public export
(Quote val tm) => Quote (Tel as val) (Tel as tm) where
  quote s [] = []
  quote s (x :: xs) = quote s x :: quote (SS s) xs

public export
Eval over tm val => Eval over (Spine as tm) (Spine as val) where
  eval env [] = []
  eval env (x :: xs) = eval env x :: eval env xs

public export
Quote val tm => Quote (Spine as val) (Spine as tm) where
  quote s [] = []
  quote s (x :: xs) = quote s x :: quote s xs

public export
Quote Lvl Idx where
  quote = lvlToIdx

-- Finding variables by name through auto implicits!

public export
interface In (0 n : String) (0 ns : Ctx) where
  idx : Idx ns

public export
In n (ns :< (m, n)) where
  idx = IZ

public export
(In n ns) => In n (ns :< n') where
  idx @{f} = IS (idx @{f})
