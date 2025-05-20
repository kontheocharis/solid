-- Definition of the surface syntax of the language
module Surface.Presyntax

import Utils
import Common
import Surface.Text
import Data.String
import Data.SnocList
import Data.DPair

public export
data PTm : Type

public export
0 PTy : Type
PTy = PTm

public export
0 PPat : Type
PPat = PTm

-- We use PTel/PParam and PSpine/PArg for both function domains and arguments,
-- as well as product types and pairs.
--
-- In order to distinguish the two for formatting purposes, we discriminate
-- with this enum.
public export
data Target = Functions | Pairs

-- A parameter like x : A
--
-- Remember: Ident holds a PiMode value as well.
public export
record PParam (t : Target) where
  constructor MkPParam
  loc : Loc
  name : Ident
  ty : Maybe PTy

-- An argument like x = a
public export
record PArg (t : Target) where
  constructor MkPArg
  loc : Loc
  name : Maybe Ident
  value : PTm

-- A sequence of parameters like (x : A, y : B)
public export
record PTel (t : Target) where
  constructor MkPTel
  actual : List (PParam t)

-- A sequence of arguments like (x = a, b)
public export
record PSpine (t : Target) where
  constructor MkPSpine
  actual : List (PArg t)

-- Varius flags for let statements
public export
record LetFlags where
  constructor MkLetFlags
  -- Which stage to bind the let in
  stage : Maybe Stage
  -- Whether the RHS is irrelevant, and if so we can extract its value as long
  -- as the rest of the block is zero-sized.
  irr : Bool

public export
letFlagsAreDefault : LetFlags -> Bool
letFlagsAreDefault (MkLetFlags Nothing False) = True
letFlagsAreDefault _ = False

-- Binary operators
--
-- @@Todo: Actually use this
public export
data BinOp = Times | Plus

-- A block is a sequence of assignment-like things. It is written like
-- { x1 := a1; ... ; xn := an; y }, similar to Rust.
public export
data PBlockStatement : Type where
  -- Recursive let statement
  --
  -- x : A
  -- x = a
  PLetRec : Loc -> LetFlags -> (name : String) -> PTy -> PTm -> PBlockStatement
  -- Let statement
  --
  -- x : A = a
  -- or
  -- x := a
  PLet : Loc -> LetFlags -> (name : String) -> Maybe PTy -> PTm -> PBlockStatement
  -- Monadic bind statement
  --
  -- x : A <- a
  -- or
  -- x <- a
  PBind : Loc -> (name : String) -> Maybe PTy -> PTm -> PBlockStatement

-- Main syntax tree, pretty self explanatory
--
-- All the binders have a gathered list of parameters.
public export
data PTm : Type where
  PName : String -> PTm
  PLam : PTel Functions -> PTm -> PTm
  PApp : PTm -> PSpine Functions -> PTm
  PPi : PTel Functions -> PTy -> PTy
  -- This stands for both types and terms
  PUnit : PTm
  -- If there is a single element these are elaborated to their contents.
  -- If there are none, it is the unit.
  -- Otherwise it is an iterated pair type.
  PSigmas : PTel Pairs -> PTy
  PPairs : PSpine Pairs -> PTm
  PHole : (name : Maybe String) -> PTy
  PBlock : (topLevel : Bool) -> List PBlockStatement -> PTm -> PTm
  -- Projection e.g. x.n : A where x : (.., n : A, ...)
  PProj : PTm -> (field : String) -> PTm
  PLoc : Loc -> PTm -> PTm

public export
Show PTm

-- Whether the term can always be unambiguously printed without parentheses
public export total
isAtomic : PTm -> Bool
isAtomic (PName _) = True
isAtomic (PSigmas _) = True
isAtomic PUnit = True
isAtomic (PHole _) = True
isAtomic (PPairs _) = True
isAtomic (PBlock False _ _) = True
isAtomic (PProj _ _) = True
isAtomic (PLoc _ t) = isAtomic t
isAtomic _ = False

public export covering
showAtomic : PTm -> String
showAtomic t = if isAtomic t then show t else "(" ++ show t ++ ")"

-- Parameters and arguments are printed differently depending on the target

public export covering
Show (PParam Functions) where
  show (MkPParam l (Explicit, n) (Just t)) = "(" ++ n ++ " : " ++ show t ++ ")"
  show (MkPParam l (Explicit, "_") (Just t)) = showAtomic t
  show (MkPParam l (Implicit, n) (Just t)) = "[" ++ n ++ " : " ++ show t ++ "]"
  show (MkPParam l (Explicit, n) Nothing) = "(" ++ n ++ " : _)"
  show (MkPParam l (Implicit, n) Nothing) = "[" ++ n ++ "]"

public export covering
Show (PParam Pairs) where
  show (MkPParam l (Explicit, n) (Just t)) = n ++ " : " ++ show t
  show (MkPParam l (Explicit, "_") (Just t)) = show t
  show (MkPParam l (Implicit, n) (Just t)) = "[" ++ n ++ "] : " ++ show t
  show (MkPParam l (Explicit, n) Nothing) = n ++ " : _"
  show (MkPParam l (Implicit, n) Nothing) = "[" ++ n ++ "]"

public export covering
Show (PArg Functions) where
  show (MkPArg l (Just (Explicit, n)) t) = "(" ++ n ++ " = " ++ show t ++ ")"
  show (MkPArg l (Just (Implicit, n)) t) = "[" ++ n ++ " = " ++ show t ++ "]"
  show (MkPArg l Nothing t) = showAtomic t

public export covering
Show (PArg Pairs) where
  show (MkPArg l (Just (Explicit, n)) t) = n ++ " = " ++ show t
  show (MkPArg l (Just (Implicit, n)) t) = "[" ++ n ++ "] = " ++ show t
  show (MkPArg l Nothing t) = show t

-- [A] (x : A) [z : B]
public export covering
Show (PTel Functions) where
  show (MkPTel []) = ""
  show (MkPTel ts) = (map show ts |> cast |> joinBy " ")

-- ([A], x : A, [z] : B)
public export covering
Show (PTel Pairs) where
  show (MkPTel ts) = "(" ++ (map show ts |> cast |> joinBy ", ") ++ ")"

-- [a = a'] x' [z = z']
public export covering
Show (PSpine Functions) where
  show (MkPSpine []) = ""
  show (MkPSpine ts) = (map show ts |> cast |> joinBy " ")

-- ([a] = a', x', [z] = b)
public export covering
Show (PSpine Pairs) where
  show (MkPSpine ts) = "(" ++ (map show ts |> cast |> joinBy ", ") ++ ")"

-- Calculate prefix flags to let statements
public export total
showLetFlags : LetFlags -> String
showLetFlags (MkLetFlags s i) =
  let result = catMaybes [stage s, irr i] |> joinBy " " in
  if result == "" then "" else result ++ " "
where
  stage : Maybe Stage -> Maybe String
  stage Nothing = Nothing
  stage (Just Obj) = Just "obj"
  stage (Just Mta) = Just "mta"

  irr : Bool -> Maybe String
  irr False = Nothing
  irr True = Just "irr"

public export covering
Show PBlockStatement where
  show (PLetRec _ f n ty v) = showLetFlags f ++ n ++ " : " ++ show ty ++ "\n" ++ n ++ " = " ++ show v
  show (PLet _ f n Nothing v) = showLetFlags f ++ n ++ " := " ++ show v
  show (PLet _ f n (Just ty) v) = showLetFlags f ++ n ++ " : " ++ show ty ++ " = " ++ show v
  show (PBind _ n (Just ty) v) = n ++ " : " ++ show ty ++ " <- " ++ show v
  show (PBind _ n Nothing v) = n ++ " <- " ++ show v

public export total
Show BinOp where
  show Times = "*"
  show Plus = "+"

public export covering
Show PTm where
  show (PName n) = n
  show (PLam args ret) = "\\" ++ show args ++ " => " ++ show ret
  show (PApp s (MkPSpine [])) = show s
  show (PApp s sp) = showAtomic s ++ " " ++ show sp
  show (PPi p b) = show p ++ " -> " ++ show b
  show (PSigmas t) = show t
  show (PPairs sp) = show sp
  show (PUnit) = "()"
  show (PBlock True h t) = (map show h |> joinBy "\n\n") ++ "\n\n" ++ show t
  show (PBlock False h t) = "{" ++ indented ((map show h |> joinBy ";\n") ++ ";\n" ++ show t) ++ "}"
  show (PHole (Just n)) = "?" ++ n
  show (PHole Nothing) = "?"
  show (PProj t n) = showAtomic t ++ "." ++ n
  show (PLoc _ t) = show t
