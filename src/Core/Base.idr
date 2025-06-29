-- Helper definitions related to working with the core language
module Core.Base

import Decidable.Equality
import Decidable.Decidable
import Data.Singleton
import Control.Monad.Identity
import Utils
import Common
import Data.HashMap

%default total

-- A context skeleton.
--
-- This will usually be marked computationally irrelevant.
-- Used to make syntax well-scoped.
public export
0 Ctx : Type
Ctx = SnocList Ident

-- An arity is a context skeleton linked forward instead of backward.
--
-- This is to avoid green slime like [< x] ++ xs in later definitions.
public export
0 Arity : Type
Arity = List Ident

export infixl 7 ::<

public export
arityToCtx : Arity -> Ctx
arityToCtx [] = [<]
arityToCtx (a :: as) = [< a] ++ arityToCtx as

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

public export
DecEq (Idx ns) where
  decEq IZ IZ = Yes Refl
  decEq (IS l) (IS l') with (decEq l l')
    decEq (IS l) (IS l) | Yes Refl = Yes Refl
    _ | No contra = No (\Refl => contra Refl)
  decEq (IS l) IZ = No (\Refl impossible)
  decEq IZ (IS l) = No (\Refl impossible)

-- De-Brujin levels.
--
-- Careful! LZ does not index the name n!
-- Rather the first element of (ns :< n).
public export
data Lvl : Ctx -> Type where
  LZ : Lvl (ns :< n)
  LS : Lvl ns -> Lvl (ns :< n)

public export
DecEq (Lvl ns) where
  decEq LZ LZ = Yes Refl
  decEq (LS l) (LS l') with (decEq l l')
    decEq (LS l) (LS l) | Yes Refl = Yes Refl
    _ | No contra = No (\Refl => contra Refl)
  decEq (LS l) LZ = No (\Refl impossible)
  decEq LZ (LS l) = No (\Refl impossible)

-- Remember only the size of a context skeleton.
public export
data Size : Ctx -> Type where
  SZ : Size [<]
  SS : Size ns -> Size (ns :< n)
  
public export
(.size) : (ns : Ctx) -> Size ns
[<] .size = SZ
(ns :< n) .size = SS (ns.size)

public export
data Count : Arity -> Type where
  CZ : Count []
  CS : Count ar -> Count (a :: ar)
  
public export
(.count) : (a : Arity) -> Count a
[] .count = CZ
(a :: as) .count = CS (as .count)
  
public export
(+) : Size ns -> Count ar -> Size (ns ::< ar)
s + CZ = s
s + (CS c) = SS s + c

public export
getIdx : (ns : Ctx) -> Idx ns -> Ident
getIdx (xs :< x) IZ = x
getIdx (xs :< x) (IS i) = getIdx xs i

-- Some de-Brujin helpers:

-- Give the first index in the context---least recently added variable.
public export
firstIdx : Size ns -> Idx (ns :< n)
firstIdx SZ = IZ
firstIdx (SS n) = IS (firstIdx n)

-- Give the next index (i.e. the index of the element after the given one).
public export
nextIdx : Idx ns -> Idx (ns :< n)
nextIdx IZ = IZ
nextIdx (IS i) = IS (nextIdx i)

-- Get the corresponding index for a level in the context.
public export
lvlToIdx : Size ns -> Lvl ns -> Idx ns
lvlToIdx (SS n) LZ = firstIdx n
lvlToIdx (SS n) (LS l) = nextIdx (lvlToIdx n l)

-- Weaken the level, points to the same element in an extended context
public export
wkLvl : Lvl us -> Lvl (us :< u)
wkLvl LZ = LZ
wkLvl (LS l) = LS (wkLvl l)

-- Give the last level in the context---most recently added variable.
public export
lastLvl : Size ns -> Lvl (ns :< n)
lastLvl SZ = LZ
lastLvl (SS n) = LS (lastLvl n)

public export
idxToLvl : Size ns -> Idx ns -> Lvl ns
idxToLvl (SS n) IZ = lastLvl n
idxToLvl (SS n) (IS i) = wkLvl (idxToLvl n i)

-- Telescopes, spines, contexts and substitutions parameterised over
-- the actual syntax they contain

namespace Tel
  public export
  data Tel : Arity -> (Ctx -> Type) -> Ctx -> Type where
    Nil : Tel [] f ms
    (::) : (Singleton a, f ms) -> Tel ar f (ms :< a) -> Tel (a :: ar) f ms
    
  public export
  %hint
  (.count) : Tel ar f ns -> Count ar
  (.count) [] = CZ
  (.count) (x :: xs) = CS xs.count


namespace Spine
  public export
  data Spine : Arity -> (Ctx -> Type) -> Ctx -> Type where
    Nil : Spine [] f ns
    (::) : (Singleton a, f ns) -> Spine ar f ns -> Spine (a :: ar) f ns

  public export
  (++) : Spine ar f ns -> Spine bs f ns -> Spine (ar ++ bs) f ns
  [] ++ sp' = sp'
  (x :: sp) ++ sp' = x :: (sp ++ sp')

  public export
  %hint
  (.count) : Spine ar f ns -> Count ar
  (.count) [] = CZ
  (.count) (x :: xs) = CS xs.count

  public export
  traverseSpine : Applicative m => (f ns -> m (g ns')) -> Spine ar f ns -> m (Spine ar g ns')
  traverseSpine f [] = pure []
  traverseSpine f ((n, x) :: xs) = [| ((n, ) <$> f x) :: traverseSpine f xs |]

  public export
  map : (f ns -> g ns') -> Spine ar f ns -> Spine ar g ns'
  map f sp = (traverseSpine (Id . f) sp).runIdentity


namespace Con
  public export
  data Con : (Ctx -> Type) -> Ctx -> Type where
    Lin : Con f [<]
    (:<) : Con f ar -> f ar -> Con f (ar :< a)

namespace Sub
  public export
  data Sub : Ctx -> (Ctx -> Type) -> Ctx -> Type where
    Lin : Sub ns f [<]
    (:<) : Sub ns f ms -> f ns -> Sub ns f (ms :< m)

  public export
  (++) : Sub ns f ms -> Sub ns f ms' -> Sub ns f (ms ++ ms')
  s ++ [<] = s
  s ++ (xs :< x) = (s ++ xs) :< x
  
  public export
  (::<) : Sub ns f ms -> Spine ar f ns -> Sub ns f (ms ::< ar)
  s ::< [] = s
  s ::< ((_, x) :: xs) = s :< x ::< xs

  public export
  (.size) : Sub ns f ms -> Size ms
  (.size) [<] = SZ
  (.size) (xs :< x) = SS xs.size

  -- Index into a substitution
  public export
  (.index) : Sub ns f ms -> Idx ms -> f ns
  (.index) (xs :< x) IZ = x
  (.index) (xs :< x) (IS i) = .index xs i
  
  public export
  mapSub : (forall us . f us -> g us) -> Sub ns f ms -> Sub ns g ms
  mapSub f [<] = [<]
  mapSub f (xs :< x) = mapSub f xs :< f x

public export
subFromSpine : Spine ar f ns -> Sub ns f (arityToCtx ar)
subFromSpine [] = [<]
subFromSpine ((_, x) :: xs) = [< x] ++ subFromSpine xs

-- Weakenings
--
-- These are technically free for de-Bruijn levels. We must use %transform on a
-- bunch of stuff to make sure.
namespace Wk
  public export
  data Wk : Ctx -> Ctx -> Type where
    Id : Wk ns ns
    Terminal : Wk ns [<]
    Drop : Wk ns ms -> Wk (ns :< n) ms

  public export
  (.) : Wk ms ns -> Wk as ms -> Wk as ns
  x . Id = x
  Id . x = x
  Terminal . Terminal = Terminal
  Terminal . Drop x = Terminal
  Drop x . Drop y = Drop (x . (Drop Id . y))

-- Some interfaces for syntax that involves variables

-- Weakening
public export
interface Weak (0 tm : Ctx -> Type) where
  weak : Wk ns ms -> tm ms -> tm ns

-- Weakening when knowing the size of the source context.
public export
interface WeakSized (0 tm : Ctx -> Type) where
  weakS : Size ns => Size ms => Wk ns ms -> tm ms -> tm ns
  
public export
Weak tm => WeakSized tm where
  weakS = weak

public export
(x : Type) => Weak (const x) where
  weak l x = x

public export
(.) : Weak tm => Sub ms tm qs -> Wk ns ms -> Sub ns tm qs
[<] . e = [<]
(xs :< x) . e = xs . e :< weak e x

export infixr 9 `o`

public export
o : WeakSized tm => Size ns => Size ms => Sub ms tm qs -> Wk ns ms -> Sub ns tm qs
o [<] e = [<]
o (xs :< x) e = xs `o` e :< weakS e x

public export
wk : Weak tm => tm ns -> tm (ns :< n)
wk x = weak (Drop Id) x

public export
wkS : WeakSized tm => Size ns => tm ns -> tm (ns :< n)
wkS = weakS (Drop Id)

-- Syntax supports variables if it supports weakenings and the zero-th deBrujin
-- index.
public export
interface (WeakSized tm) => Vars (0 tm : Ctx -> Type) where
  here : (sz : Size ns) => tm (ns :< n)

public export
lift : (Weak tm, Vars tm) => (sz : Size ns) => Sub ns tm ms -> Sub (ns :< a) tm (ms :< a')
lift env = env . Drop Id :< here

public export
liftS : (WeakSized tm, Vars tm) => (sz : Size ns) => Sub ns tm ms -> Sub (ns :< a) tm (ms :< a')
liftS env = env `o` (Drop Id) :< here

public export
id : (Weak tm, Vars tm) => (sz : Size ns) => Sub ns tm ns
id {sz = SZ} = [<]
id {sz = SS k} = lift {sz = k} (id {sz = k})

public export
idS : (WeakSized tm, Vars tm) => (sz : Size ns) => Sub ns tm ns
idS {sz = SZ} = [<]
idS {sz = SS k} = liftS {sz = k} (idS {sz = k})

public export
proj : (Weak tm, Vars tm) => Size ns => Sub (ns :< n) tm ns
proj = id . Drop Id

-- Index into a context
namespace Con
  public export
  (.index) : Weak f => Con f ms -> Idx ms -> f ms
  (.index) (xs :< x) IZ = wk x
  (.index) (xs :< x) (IS i) = wk (xs.index i)

  public export
  (.indexS) : WeakSized f => (s : Size ms) => Con f ms -> Idx ms -> f ms
  (.indexS) {s = SS ms} (xs :< x) IZ = wkS x
  (.indexS) {s = SS ms} (xs :< x) (IS i) = wkS (xs.indexS i)

-- Evaluation and quoting interfaces

public export
interface Eval (0 over : Ctx -> Type) (0 tm : Ctx -> Type) (0 val : Ctx -> Type) | tm, val where
  eval : Sub ns over ms -> tm ms -> val ns
  
public export
interface EvalSized (0 over : Ctx -> Type) (0 tm : Ctx -> Type) (0 val : Ctx -> Type) | tm, val where
  evalS : Size ns => Size ms => Sub ns over ms -> tm ms -> val ns
  
-- Shorthand for evaluation when src and target are the same.
public export
sub : EvalSized over tm tm => (sns : Size ns) => (sms : Size ms) => Sub ns over ms -> tm ms -> tm ns
sub = evalS

public export
Eval over tm val => EvalSized over tm val where
  evalS = eval

public export
interface Quote (0 val : Ctx -> Type) (0 tm : Ctx -> Type) where
  quote : (sz : Size ns) => val ns -> tm ns
  

-- Supporting evaluation and quoting gives us normalisation
nf : (Weak over, Vars over, EvalSized over tm val, Quote val tm) => Size ns => tm ns -> tm ns
nf @{(_, _, e, _)} @{s} tm = quote (evalS @{e} id tm)

-- Relabeling should always be the identity

public export
data Relab : Ctx -> Ctx -> Type where
  Id : Relab ns ns
  Keep : Relab ns ms -> Relab (ns :< n) (ms :< n)
  Change : (0 n : Ident) -> Relab ns ms -> Relab (ns :< n) (ms :< n')

public export  
keepMany : Count ar => Relab ns ms -> Relab (ns ::< ar) (ms ::< ar)
keepMany @{CZ} r = r
keepMany @{CS n} r = keepMany @{n} (Keep r)
  
public export
interface Relabel (0 tm : Ctx -> Type) where
  relabel : Relab ns ms -> tm ms -> tm ns
  
namespace Relabel
  public export
  (.) : Relabel tm => Relab ns ms -> Sub ms tm qs -> Sub ns tm qs
  r . [<] = [<]
  r . (xs :< x) = r . xs :< relabel r x

-- Basic implementations for the defined types


public export
Relabel Idx where
  relabel Id i = i
  relabel (Change _ x) (IS i) = IS (relabel x i)
  relabel (Change _ x) IZ = IZ
  relabel (Keep x) (IS i) = IS (relabel x i)
  relabel (Keep x) IZ = IZ
  
public export
Relabel Lvl where
  relabel Id i = i
  relabel (Change _ x) (LS i) = LS (relabel x i)
  relabel (Change _ x) LZ = LZ
  relabel (Keep x) (LS i) = LS (relabel x i)
  relabel (Keep x) LZ = LZ

public export
Weak Lvl where
  -- @@Todo: use %transform, do not rely on identity optimisation
  weak Id l = l
  weak (Drop x) LZ = LZ
  weak (Drop x) (LS l) = LS (weak x (wkLvl l))
  
public export
Weak Idx where
  weak Id x = x
  weak (Drop x) u = IS (weak x u)

public export
Vars Lvl where
  here {sz = s} = lastLvl s
  
public export
Vars Idx where
  here {sz = s} = IZ

public export
Quote Lvl Idx where
  quote {sz = sz} = lvlToIdx sz
  
public export
Relabel tm => Relabel (Spine ar tm) where
  relabel r sp = map (relabel r) sp

public export
(Weak tm) => Weak (Spine ar tm) where
  weak e sp = map (weak e) sp

public export
(WeakSized tm) => WeakSized (Spine ar tm) where
  weakS e sp = map (weakS e) sp

public export
Eval over tm val => Eval over (Spine ar tm) (Spine ar val) where
  eval env sp = map (eval env) sp

public export
(WeakSized over, Vars over, EvalSized over tm val) => EvalSized over (Tel ar tm) (Tel ar val) where
  evalS env [] = []
  evalS env ((n, x) :: xs) = (n, evalS env x) :: evalS (liftS env) xs

public export
Quote val tm => Quote (Spine ar val) (Spine ar tm) where
  quote sp = map quote sp
  
public export
Relabel tm => Relabel (Tel ar tm) where
  relabel r [] = []
  relabel r ((n, x) :: xs) = (n, relabel r x) :: relabel (Keep r) xs

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

-- Metavariables

public export
data MetaVar : Type where
  UserGiven : (Nat, String) -> MetaVar
  AutoGenerated : Nat -> MetaVar
  
export
Hashable MetaVar where
  hashWithSalt s (UserGiven f) = hashWithSalt s f
  hashWithSalt s (AutoGenerated n) = hashWithSalt s n

export
Eq MetaVar where
  (UserGiven (n, s)) == (UserGiven (n', s')) = n == n' && s == s'
  (AutoGenerated n) == (AutoGenerated n') = n == n'
  _ == _ = False