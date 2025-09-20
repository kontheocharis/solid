module Utils

import Data.Singleton
import Data.Fin
import Data.String
import Control.Monad.State
import Data.HashMap

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
data Input : Type where
  FileInput : (filename : String) -> Input
  
public export
Show Input where
  show (FileInput filename) = "File input: " ++ filename
  
export
Hashable Input where
  hashWithSalt s (FileInput f) = hashWithSalt s f

export
Eq Input where
  (FileInput n) == (FileInput n') = n == n'
  _ == _ = False

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

-- Composable MonadState

public export
interface Monad m => HasState s m where
  get' : m s
  put : s -> m ()

  state : (s -> (s, a)) -> m a
  state f = do
    u <- get' {s = s}
    let (u', a) = f u
    put u'
    pure a
    
public export
get : (0 s : Type) -> HasState s m => m s
get s = get' {s = s}

-- Apply a function to modify the context of this computation
public export
modify : HasState s m => (s -> s) -> m ()
modify f = do
  s <- get s
  put (f s)

-- Evaluate a function in the context held by this computation
public export
gets : HasState s m => (s -> a) -> m a
gets f = do
  s <- get s
  pure (f s)
  
-- Lenses

public export
record Lens (s : Type) (s' : Type) where
  constructor MkLens
  get : s -> s'
  set : s' -> s -> s
  
export
idL : Lens s s
idL = MkLens id (\a, b => a)
  
export
access : HasState s m => Lens s s' -> m s'
access (MkLens gt _) = gets gt
  
export
set : HasState s m => Lens s s' -> s' -> m ()
set (MkLens gt st) v = modify (st v)

export
map : Lens s s' -> (s' -> s') -> s -> s
map (MkLens gt st) f x = st (f (gt x)) x
  
export
update : HasState s m => Lens s s' -> (s' -> s') -> m ()
update l v = modify (map l v)
  
export
reset : HasState s m => Lens s (Maybe s') -> m (Maybe s')
reset (MkLens gt st) = do
  s <- get s
  put (st Nothing s)
  pure $ gt s

export
enter : HasState s m => Lens s s' -> s' -> m a -> m a
enter (MkLens _ st) val f = do
  s1 <- get s
  put (st val s1)
  x <- f
  s2 <- get s
  put (st val s2)
  pure x
  
export
(.) : Lens s s' -> Lens s' s'' -> Lens s s''
(MkLens gt' st') . (MkLens gt st) = MkLens (gt . gt') (\a, b => st' (st a (gt' b)) b)

-- Resolvers
--
-- A resolver tries to resolve something, and if it can't it returns Nothing. We
-- can combine resolvers by trying one after the other until one succeeds. When
-- combining, if one resolver makes a change, we restart the whole process.
--
-- Resolvers should have the property that if they succeed, they will return 
-- `Nothing` when applied to their own output.

public export
record Resolver m a where
  constructor MkResolver
  tryResolve : a -> m (Maybe a)
  
export covering
Monad m => Semigroup (Resolver m a) where
  (MkResolver r1) <+> (MkResolver r2) = MkResolver go
    where
      go : a -> m (Maybe a)
      go x = do
        mx' <- r1 x
        case mx' of
          Just x' => do
            mx'' <- r2 x'
            case mx'' of
              Just x'' => go x'' >>= \case
                Just x''' => pure (Just x''')
                Nothing => pure (Just x')
              Nothing => pure (Just x')
          Nothing => do
            mx'' <- r2 x
            case mx'' of
              Just x'' => go x'' >>= \case
                Just x''' => pure (Just x''')
                Nothing => pure (Just x'')
              Nothing => pure Nothing
  
export
Monad m => Monoid (Resolver m a) where
  neutral = MkResolver (\x => pure Nothing)
  
export covering
repeatedly : Monad m => (a -> m (Maybe a)) -> Resolver m a
repeatedly f = MkResolver go
  where
    go : a -> m (Maybe a)
    go x = do
      mx' <- f x
      case mx' of
        Just x' => go x' >>= \case
          Just x'' => pure (Just x'')
          Nothing => pure (Just x')
        Nothing => pure Nothing

%inline
export covering
resolve : Monad m => Resolver m a -> a -> m a
resolve r x = fromMaybe x <$> r.tryResolve x
  
-- Other stuff
export
nothingIsNotJust : Nothing = Just x -> Void
nothingIsNotJust Refl impossible