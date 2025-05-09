module Surface.Text

import Data.Fin
import Data.String

-- Text stuff

public export
indented : String -> String
indented s = (lines ("\n" ++ s) |> map (\l => "  " ++ l) |> joinBy "\n") ++ "\n"

-- Source location

public export
record Loc where
  constructor MkLoc
  src : List Char
  pos : Fin (length src)

public export
dummyLoc : Loc
dummyLoc = MkLoc [' '] (FZ)

public export
linesBefore : Loc -> List String
linesBefore loc = lines (substr 0 (finToNat loc.pos) (pack loc.src))

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
