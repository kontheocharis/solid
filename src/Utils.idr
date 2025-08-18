module Utils

import Data.Singleton
import Data.Fin
import Data.String
import Control.Monad.State

%default total

public export
error : String -> a
error x = assert_total (idris_crash x)

-- | A literal
public export
data Lit = Str String | Chr Char | Num Nat

public export
Show Lit where
  show (Str s) = show s
  show (Chr c) = show c
  show (Num n) = show n

-- Singletons extra

public export
(.value) : {0 x : a} -> Singleton x -> a
(.value) (Val x) = x

public export
(.identity) : {0 x : a} -> (s : Singleton x) -> s.value = x
(.identity) (Val y) = Refl

public export
decToSemiDec : Dec a -> Maybe a
decToSemiDec (Yes x) = Just x
decToSemiDec (No _) = Nothing

public export
interface SemiDecEq a where
  semiDecEq : (x : a) -> (y : a) -> Maybe (x = y)

-- Text stuff

public export
indented : String -> String
indented s = (lines ("\n" ++ s) |> map (\l => "  " ++ l) |> joinBy "\n") ++ "\n"

-- Source location

public export
record Loc where
  constructor MkLoc
  src : List Char
  pos : Nat -- not necessarily in range

public export
dummyLoc : Loc
dummyLoc = MkLoc [] Z

public export
linesBefore : Loc -> List String
linesBefore loc = lines (substr 0 loc.pos (pack loc.src))

public export
(.row) : Loc -> Nat
(.row) loc = length (linesBefore loc)

public export
(.col) : Loc -> Nat
(.col) loc = case linesBefore loc of
  [] => 1
  (x::xs) => length (last (x::xs)) + 1

export
Show Loc where
  show m = "line " ++ show m.row ++ ", column " ++ show m.col

namespace Foo
public export
data DispList : List a -> Type -> Type where
  Nil : DispList [] b
  (::) : b -> DispList xs b -> DispList (x :: xs) b
  
public export
dispToList : {xs : List a} -> DispList xs b -> List (a, b)
dispToList [] = []
dispToList {xs = x :: _} (l :: ls) = (x, l) :: dispToList ls

public export
data DispSnocList : SnocList a -> Type -> Type where
  Lin : DispSnocList [<] b
  (:<) : DispSnocList xs b -> b -> DispSnocList (xs :< x) b
  
public export
dispToSnocList : {xs : SnocList a} -> DispSnocList xs b -> SnocList (a, b)
dispToSnocList [<] = [<]
dispToSnocList {xs = _ :< x} (ls :< l) = dispToSnocList ls :< (x, l)

-- Some state utilities

public export
record Lens (s : Type) (s' : Type) where
  constructor MkLens
  get : s -> s'
  set : s' -> s -> s
  
export
access : MonadState s m => Lens s s' -> m s'
access (MkLens gt _) = gets gt

export
enter : MonadState s m => Lens s s' -> s' -> m a -> m a
enter (MkLens _ st) val f = do
  s1 <- get
  put (st val s1)
  x <- f
  s2 <- get
  put (st val s2)
  pure x