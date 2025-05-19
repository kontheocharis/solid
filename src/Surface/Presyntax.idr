-- Definition of the surface syntax of the language
module Surface.Presyntax

import Utils
import Core.Syntax
import Surface.Text
import Core.Base
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

namespace PTel
  public export
  (.arity) : PTel t -> Arity
  (.arity) (MkPTel p) = map (.name) p

-- Varius flags for let statements
record LetFlags where
  constructor MkLetFlags
  -- Which stage to bind the let in
  stage : Maybe Stage
  -- Whether the RHS is irrelevant, and if so we can extract its value as long
  -- as the rest of the block is zero-sized.
  irr : Bool
  -- Whether this let is recursive
  rec : Bool

-- Binary operators
data BinOp = Times | Plus

-- A block is a sequence of assignment-like things. It is written like
-- { x1 := a1; ... ; xn := an; y }, similar to Rust.
data PBlockStart : Type where
  -- Let statement
  --
  -- x : A = a
  -- or
  -- x := a
  PLet : LetFlags -> (name : String) -> Maybe PTy -> PTm -> PBlockStart
  -- Monadic bind statement
  --
  -- x : A <- a
  -- or
  -- x <- a
  PBind : (name : String) -> Maybe PTy -> PTm -> PBlockStart

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
  PBlock : (topLevel : Bool) -> List PBlockStart -> PTm -> PTm
  -- Projection e.g. x.n : A where x : (.., n : A, ...)
  PProj : PTm -> (field : String) -> PTm
  PLoc : Loc -> PTm -> PTm

public export
Show PTm

-- Whether the term can always be unambiguously printed without parentheses
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

covering
showAtomic : PTm -> String
showAtomic t = if isAtomic t then show t else "(" ++ show t ++ ")"

-- Parameters and arguments are printed differently depending on the target

public export covering
Show (PParam Functions) where
  show (MkPParam l (Explicit, n) (Just t)) = "(" ++ show n ++ " : " ++ show t ++ ")"
  show (MkPParam l (Explicit, "_") (Just t)) = showAtomic t
  show (MkPParam l (Implicit, n) (Just t)) = "[" ++ show n ++ " : " ++ show t ++ "]"
  show (MkPParam l (Explicit, n) Nothing) = "(" ++ show n ++ " : _)"
  show (MkPParam l (Implicit, n) Nothing) = "[" ++ show n ++ "]"

public export covering
Show (PParam Pairs) where
  show (MkPParam l (Explicit, n) (Just t)) = show n ++ " : " ++ show t
  show (MkPParam l (Explicit, "_") (Just t)) = show t
  show (MkPParam l (Implicit, n) (Just t)) = "[" ++ show n ++ "] : " ++ show t
  show (MkPParam l (Explicit, n) Nothing) = show n ++ " : _"
  show (MkPParam l (Implicit, n) Nothing) = "[" ++ show n ++ "]"

public export covering
Show (PArg Functions) where
  show (MkPArg l (Just (Explicit, n)) t) = "(" ++ show n ++ " = " ++ show t ++ ")"
  show (MkPArg l (Just (Implicit, n)) t) = "[" ++ show n ++ " = " ++ show t ++ "]"
  show (MkPArg l Nothing t) = showAtomic t

public export covering
Show (PArg Pairs) where
  show (MkPArg l (Just (Explicit, n)) t) = show n ++ " = " ++ show t
  show (MkPArg l (Just (Implicit, n)) t) = "[" ++ show n ++ "] = " ++ show t
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
showLetFlags : LetFlags -> String
showLetFlags (MkLetFlags s r i) =
  let result = catMaybes [stage s, rec r, irr i] |> joinBy " " in
  if result == "" then "" else result ++ " "
where
  stage : Maybe Stage -> Maybe String
  stage Nothing = Nothing
  stage (Just Obj) = Just "obj"
  stage (Just Mta) = Just "mta"

  rec : Bool -> Maybe String
  rec False = Nothing
  rec True = Just "rec"

  irr : Bool -> Maybe String
  irr False = Nothing
  irr True = Just "irr"

public export covering
Show PBlockStart where
  show (PLet f n Nothing v) = showLetFlags f ++ show n ++ " := " ++ show v
  show (PLet f n (Just ty) v) = showLetFlags f ++ show n ++ " : " ++ show ty ++ " = " ++ show v
  show (PBind n (Just ty) v) = show n ++ " : " ++ show ty ++ " <- " ++ show v
  show (PBind n Nothing v) = show n ++ " <- " ++ show v

public export covering
Show PTm where
  show (PName n) = show n
  show (PLam args ret) = "\\" ++ show args ++ " => " ++ show ret
  show (PApp s sp) = showAtomic s ++ show sp
  show (PPi p b) = show p ++ " -> " ++ show b
  show (PSigmas t) = show t
  show (PPairs sp) = show sp
  show (PUnit) = "()"
  show (PBlock True h t) = (map show h |> joinBy ";\n") ++ show t
  show (PBlock False h t) = "{\n" ++ indented ((map show h |> joinBy ";\n") ++ show t) ++ "\n}"
  show (PHole (Just n)) = "?" ++ n
  show (PHole Nothing) = "?"
  show (PProj t n) = showAtomic t ++ "." ++ n
  show (PLoc _ t) = show t
