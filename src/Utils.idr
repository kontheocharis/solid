module Utils

import Data.Singleton

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
