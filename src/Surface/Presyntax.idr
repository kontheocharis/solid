module Surface.Presyntax

import Core.Syntax
import Surface.Text
import Core.Context
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


public export
record PParam where
  constructor MkPParam
  loc : Loc
  name : Ident
  ty : Maybe PTy

public export
record PTel where
  constructor MkPTel
  actual : List PParam

namespace PTel
  public export
  (.arity) : PTel -> Arity
  (.arity) (MkPTel p) = map (.name) p

record LetFlags where
  constructor MkLetFlags
  stage : Maybe Stage
  rec : Bool
  irr : Bool

data BinOp : Type where
  Times : BinOp
  Plus : BinOp




public export
data PTm : Type where
  PIdent : String -> PTm
  PLam : Ident -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : PParam -> PTy -> PTy
  PSigma : PParam -> PTy -> PTy
  PLoc : Loc -> PTm -> PTm
  PLet : LetFlags -> (name : String) -> Maybe PTy -> PTm -> PTm -> PTm
  -- PLetIrr?

public export
pApps : PTm -> SnocList PTm -> PTm
pApps f [<] = f
pApps f (xs :< x) = PApp (pApps f xs) x

public export
pGatherApps : PTm -> (PTm, SnocList PTm)
pGatherApps (PApp f x) = let (f', xs) = pGatherApps f in (f', xs :< x)
pGatherApps (PLoc _ t) = pGatherApps t
pGatherApps f = (f, [<])

public export
pGatherPis : PTy -> (PTel, PTy)
pGatherPis (PPi p b) = let (MkPTel ps, ret) = pGatherPis b in (MkPTel (p :: ps), ret)
pGatherPis t = (MkPTel [], t)

public export
pGatherLams : PTm -> (List (Ident, Maybe PTy), PTm)
pGatherLams (PLam n ty t) = let (ns, t') = pGatherLams t in ((n, ty) :: ns, t')
pGatherLams (PLoc _ t) = pGatherLams t
pGatherLams t = ([], t)

public export
pPis : PTel -> PTy -> PTy
pPis (MkPTel cs) b = foldr PPi b cs

public export
Show PTm

public export covering
Show PParam where
  show (MkPParam l (Explicit, n) (Just t)) = "(" ++ show n ++ " : " ++ show t ++ ")"
  show (MkPParam l (Explicit, "_") (Just t)) = show t
  show (MkPParam l (Implicit, n) (Just t)) = "{" ++ show n ++ " : " ++ show t ++ "}"
  show (MkPParam l (Explicit, n) Nothing) = "(" ++ show n ++ " : _)"
  show (MkPParam l (Implicit, n) Nothing) = "{" ++ show n ++ "}"

public export covering
Show PTel where
  show (MkPTel []) = ""
  show (MkPTel ts) = " " ++ (map show ts |> cast |> joinBy " ")

isAtomic : PTm -> Bool
isAtomic (PIdent _) = True
isAtomic (PLoc _ t) = isAtomic t
isAtomic _ = False

covering
showAtomic : PTm -> String

showLetFlags : LetFlags -> String
showLetFlags (MkLetFlags s r i) = catMaybes [stage s, rec r, irr i] |> joinBy " "
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
Show PTm where
  show (PIdent n) = show n
  show t@(PLam _ _ _) = let (args, ret) = pGatherLams t in "\\" ++ joinBy " " (map (\((md, n), ty) =>
        show (MkPParam dummyLoc (md, n) ty)
      ) args) ++ " => " ++ show ret
  show t@(PApp _ _) = let (s, sp) = pGatherApps t in showAtomic s ++ " " ++ joinBy " " (cast $ map showAtomic sp)
  show (PPi p b) = show p ++ " -> " ++ show b
  show (PSigma p b) = show p ++ " ** " ++ show b
  show (PLet f n Nothing v t) = showLetFlags f ++ " " ++ show n ++ " := " ++ show v ++ "; " ++ show t
  show (PLet f n (Just ty) v t) = showLetFlags f ++ " " ++ show n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show (PLoc _ t) = show t

showAtomic t = if isAtomic t then show t else "(" ++ show t ++ ")"
