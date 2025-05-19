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

data Target : Type where
  Functions : Target
  Pairs : Target

public export
record PParam (t : Target) where
  constructor MkPParam
  loc : Loc
  name : Ident
  ty : Maybe PTy

public export
record PArg (t : Target) where
  constructor MkPArg
  loc : Loc
  name : Maybe Ident
  value : PTm

public export
record PTel (t : Target) where
  constructor MkPTel
  actual : List (PParam t)

public export
record PSpine (t : Target) where
  constructor MkPSpine
  actual : List (PArg t)

namespace PTel
  public export
  (.arity) : PTel t -> Arity
  (.arity) (MkPTel p) = map (.name) p

record LetFlags where
  constructor MkLetFlags
  stage : Maybe Stage
  irr : Bool
  rec : Bool

data BinOp = Times | Plus

data PBlockStart : Type where
  PLet : LetFlags -> (name : String) -> Maybe PTy -> PTm -> PBlockStart
  PBind : (name : String) -> Maybe PTy -> PTm -> PBlockStart

public export
data PTm : Type where
  PName : String -> PTm
  PLam : PTel Functions -> PTm -> PTm
  PApp : PTm -> PSpine Functions -> PTm
  PPi : PTel Functions -> PTy -> PTy
  PUnit : PTy
  PSigmas : PTel Pairs -> PTy
  PPairs : PSpine Pairs -> PTm
  PHole : (name : Maybe String) -> PTy
  PBlock : (topLevel : Bool) -> List PBlockStart -> PTm -> PTm
  PProj : PTm -> (field : String) -> PTm
  PLoc : Loc -> PTm -> PTm

public export
Show PTm

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

public export covering
Show (PTel Functions) where
  show (MkPTel []) = ""
  show (MkPTel ts) = (map show ts |> cast |> joinBy " ")

public export covering
Show (PTel Pairs) where
  show (MkPTel ts) = "(" ++ (map show ts |> cast |> joinBy ", ") ++ ")"

public export covering
Show (PSpine Pairs) where
  show (MkPSpine ts) = "(" ++ (map show ts |> cast |> joinBy ", ") ++ ")"

public export covering
Show (PSpine Functions) where
  show (MkPSpine []) = ""
  show (MkPSpine ts) = (map show ts |> cast |> joinBy " ")

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
