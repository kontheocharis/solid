module Context

public export
data PiMode = Explicit | Implicit

public export
0 Name : Type
Name = (PiMode, String)

public export
0 Ctx : Type
Ctx = SnocList Name

public export
0 Arity : Type
Arity = List Name

infixl 7 ::<

public export
(::<) : Ctx -> Arity -> Ctx
ns ::< [] = ns
ns ::< (a :: as) = (ns :< a) ::< as

public export
data Idx : Ctx -> Type where
  IZ : Idx (ns :< n)
  IS : Idx ns -> Idx (ns :< n)

public export
data Lvl : Ctx -> Type where
  LZ : Lvl (ns :< n)
  LS : Lvl ns -> Lvl (ns :< n)

public export
data Size : Ctx -> Type where
  SZ : Size [<]
  SS : Size ns -> Size (ns :< n)

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

-- Some interfaces

public export
interface Wk (0 tm : Ctx -> Type) where
  wk : tm ns -> tm (ns :< n)

public export
interface (Wk over) => Subst (0 over : Ctx -> Type) where
  here : Size ns -> over (ns :< n)

  ext : Size ns -> Sub ns over ms -> Sub (ns :< n) over ms
  ext s [<] = [<]
  ext s (xs :< x) = ext s xs :< wk x

  lift : Size ns -> Sub ns over ms -> Sub (ns :< a) over (ms :< a)
  lift s env = ext s env :< here s

  id : Size ns -> Sub ns over ns
  id SZ = [<]
  id (SS k) = lift k (id k)

  proj : Size ns -> Sub (ns :< n) over ns
  proj s = ext s (id s)

public export
interface Eval (0 over : Ctx -> Type) (0 tm : Ctx -> Type) (0 val : Ctx -> Type) where
  eval : Sub ns over ms -> tm ms -> val ns

public export
interface Quote (0 val : Ctx -> Type) (0 tm : Ctx -> Type) where
  quote : Size ns -> val ns -> tm ns

public export
Wk Lvl where
  wk LZ = LZ
  wk (LS l) = LS (wk l)

public export
Wk Idx where
  wk = IS

public export
(Wk tm) => Wk (Spine as tm) where
  wk [] = []
  wk (x :: xs) = wk x :: wk xs

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

-- Finding variables by name

public export
interface In (0 n : String) (0 ns : Ctx) where
  idx : Idx ns

public export
In n (ns :< (m, n)) where
  idx = IZ

public export
(In n ns) => In n (ns :< n') where
  idx @{f} = IS (idx @{f})
