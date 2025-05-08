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

public export
interface Proj (0 over : Ctx -> Type) where
  proj : Sub (ns :< n) over ns

public export
interface Wk (0 tm : Ctx -> Type) where
  wk : tm ns -> tm (ns :< n)

public export
interface Lift (0 tm : Ctx -> Type) where
  lift : Sub ns tm ms -> Sub (ns :< a) tm (ms :< a')

Wk Lvl where
  wk LZ = LZ
  wk (LS l) = LS (wk l)

Wk Idx where
  wk = IS

(Wk tm) => Wk (Spine as tm) where
  wk [] = []
  wk (x :: xs) = wk x :: wk xs

public export
interface Eval (0 over : Ctx -> Type) (0 src : Ctx -> Type) (0 dest : Ctx -> Type) where
  eval : Sub ns over ms -> src ms -> dest ns

public export
(Lift over, Eval over src dest) => Eval over (Tel as src) (Tel as dest) where
  eval env [] = []
  eval env (x :: xs) = eval env x :: eval (lift env) xs

public export
Eval over src dest => Eval over (Spine as src) (Spine as dest) where
  eval env [] = []
  eval env (x :: xs) = eval env x :: eval env xs

public export
interface In (0 n : String) (0 ns : Ctx) where
  idx : Idx ns

public export
In n (ns :< (m, n)) where
  idx = IZ

public export
(In n ns) => In n (ns :< n') where
  idx @{f} = IS (idx @{f})
