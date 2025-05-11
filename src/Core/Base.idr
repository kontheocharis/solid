-- Helper definitions related to working with the core language
module Core.Base

import Decidable.Equality
import Data.Singleton
import Control.Monad.Identity
import Utils

%default total

-- A bound variable is either from an explicit or an implicit pi.
--
-- We remember this in the context.
public export
data PiMode = Explicit | Implicit

-- A name is a member of a 'context skeleton'
public export
0 Ident : Type
Ident = (PiMode, String)

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
data Count : Arity -> Type where
  CZ : Count []
  CS : Count ar -> Count (a :: ar)

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

public export
idxToLvl : Size ns -> Idx ns -> Lvl ns
idxToLvl = ?fafa


-- Give the last level in the context---most recently added variable.
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
    (::) : f ms -> Tel ar f (ms :< a) -> Tel (a :: ar) f ms

namespace Spine
  public export
  data Spine : Arity -> (Ctx -> Type) -> Ctx -> Type where
    Nil : Spine [] f ns
    (::) : f ns -> Spine ar f ns -> Spine (a :: ar) f ns

  public export
  (++) : Spine ar f ns -> Spine bs f ns -> Spine (ar ++ bs) f ns
  [] ++ sp' = sp'
  (x :: sp) ++ sp' = x :: (sp ++ sp')

  public export
  (.count) : Spine ar f ns -> Count ar
  (.count) [] = CZ
  (.count) (x :: xs) = CS xs.count

  public export
  traverseSpine : Applicative m => (f ns -> m (g ns')) -> Spine ar f ns -> m (Spine ar g ns')
  traverseSpine f [] = pure []
  traverseSpine f (x :: xs) = [| f x :: traverseSpine f xs |]

  public export
  mapSpine : (f ns -> g ns') -> Spine ar f ns -> Spine ar g ns'
  mapSpine f sp = (traverseSpine (Id . f) sp).runIdentity


namespace Con
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
subFromSpine : Spine ar f ns -> Sub ns f (arityToCtx ar)
subFromSpine [] = [<]
subFromSpine (x :: xs) = [< x] ++ subFromSpine xs

-- Weakenings
namespace Wk
  public export
  data Wk : Ctx -> Ctx -> Type where
    Id : Wk ns ns
    Drop : Wk ns ms -> Wk (ns :< n) ms

-- Some interfaces for syntax that involves variables

-- Weakening
public export
interface Weak (0 tm : Ctx -> Type) where
  weak : Wk ns ms -> tm ms -> tm ns

public export
(.) : Weak tm => Sub ms tm qs -> Wk ns ms -> Sub ns tm qs
[<] . e = [<]
(xs :< x) . e = xs . e :< weak e x

public export
wk : Weak tm => tm ns -> tm (ns :< n)
wk x = weak (Drop Id) x

-- Syntax supports variables if it supports thinnings and the zero-th deBrujin
-- index.
public export
interface (Weak tm) => Vars (0 tm : Ctx -> Type) where
  here : Size ns -> tm (ns :< n)

public export
lift : (Weak tm, Vars tm) => Size ns -> Sub ns tm ms -> Sub (ns :< a) tm (ms :< a')
lift s env = env . Drop Id :< here s

public export
id : (Weak tm, Vars tm) => Size ns -> Sub ns tm ns
id SZ = [<]
id (SS k) = lift k (id k)

public export
proj : (Weak tm, Vars tm) => Size ns -> Sub (ns :< n) tm ns
proj s = id s . Drop Id

-- Evaluation, quoting and unification interfaces

public export
interface Eval (0 over : Ctx -> Type) (0 tm : Ctx -> Type) (0 val : Ctx -> Type) where
  eval : Sub ns over ms -> tm ms -> val ns

public export
interface Quote (0 val : Ctx -> Type) (0 tm : Ctx -> Type) where
  quote : Size ns -> val ns -> tm ns

-- Basic implementations for the defined types

public export
Weak Lvl where
  -- @@Todo: use %transform, do not rely on identity optimisation
  weak Id l = l
  weak (Drop x) LZ = LZ
  weak (Drop x) (LS l) = LS (weak x (wkLvl l))
    where
      wkLvl : Lvl us -> Lvl (us :< u)
      wkLvl LZ = LZ
      wkLvl (LS l) = LS (wkLvl l)

public export
Vars Lvl where
  here s = lastLvl s

public export
Quote Lvl Idx where
  quote = lvlToIdx

public export
(Weak tm) => Weak (Spine ar tm) where
  weak e sp = mapSpine (weak e) sp

public export
Eval over tm val => Eval over (Spine ar tm) (Spine ar val) where
  eval env sp = mapSpine (eval env) sp

public export
Quote val tm => Quote (Spine ar val) (Spine ar tm) where
  quote s sp = mapSpine (quote s) sp

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


-- Unification

-- Unification outcome
--
-- Observationally means under all substitutions from the empty context.
public export
data Unification : Type where
  -- Are observationally the same
  AreSame : Unification
  -- Are observationally different
  AreDifferent : Unification
  -- Don't look the same but could become the same (or different) under
  -- appropriate substitutions
  DontKnow : Unification

-- Definitively decide a unification outcome based on a decidable equality
public export
ifAndOnlyIf : Dec (a ~=~ b) -> ((a ~=~ b) -> Unification) -> Unification
ifAndOnlyIf (Yes Refl) f = f Refl
ifAndOnlyIf (No _) _ = AreDifferent

-- Definitively decide a unification outcome based on a semi-decidable equality
--
-- This is a "hack" because really we should be providing DecEq to be sure they
-- are different. However sometimes it is super annoying to implement DecEq so
-- we just use this instead.
public export
ifAndOnlyIfHack : Maybe (a ~=~ b) -> ((a ~=~ b) -> Unification) -> Unification
ifAndOnlyIfHack (Just Refl) f = f Refl
ifAndOnlyIfHack Nothing _ = AreDifferent

-- Partially decide a unification outcome based on a semi-decidable equality
public export
inCase : Maybe (a ~=~ b) -> ((a ~=~ b) -> Unification) -> Unification
inCase (Just Refl) f = f Refl
inCase Nothing _ = DontKnow

export infixr 5 /\
export infixr 4 \/

-- Conjunction of unification outcomes
public export
(/\) : Unification -> Lazy Unification -> Unification
AreDifferent /\ x = AreDifferent
x /\ AreDifferent = AreDifferent
AreSame /\ AreSame = AreSame
DontKnow /\ AreSame = DontKnow
AreSame /\ DontKnow = DontKnow
DontKnow /\ DontKnow = DontKnow

-- Disjunction of unification outcomes
-- In particular, when this is used, we shall not solve any metas.
public export
(\/) : Unification -> Lazy Unification -> Unification
AreSame \/ x = AreSame
x \/ AreSame = AreSame
AreDifferent \/ AreDifferent = AreDifferent
DontKnow \/ AreDifferent = DontKnow
AreDifferent \/ DontKnow = DontKnow
DontKnow \/ DontKnow = DontKnow

-- The typeclass for unification
public export
interface Unify (0 lhs : Ctx -> Type) (0 rhs : Ctx -> Type) where
  unify : Size ns -> lhs ns -> rhs ns -> Unification

-- Basic implementations

public export
Unify Lvl Lvl where
  unify s l l' = ifAndOnlyIf (decEq l l') (\Refl => AreSame)

public export
Unify val val' => Unify (Spine as val) (Spine as' val') where
  unify s [] [] = AreSame
  unify s (x :: xs) (y :: ys) = unify s x y /\ unify s xs ys
  unify s _ _ = AreDifferent
