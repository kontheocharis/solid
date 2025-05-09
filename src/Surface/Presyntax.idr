module Surface.Presyntax

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
  name : Name
  ty : PTy

public export
record PTel where
  constructor MkPTel
  actual : List PParam

namespace PTel
  public export
  (.arity) : PTel -> Arity
  (.arity) (MkPTel p) = map (.name) p

public export
data PTm : Type where
  PName : String -> PTm
  PLam : Name -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : PParam -> PTy -> PTy
  PSigma : PParam -> PTy -> PTy
  PLoc : Loc -> PTm -> PTm
  PLet : String -> Maybe PTy -> PTm -> PTm -> PTm

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
pGatherLams : PTm -> (List (Name, Maybe PTy), PTm)
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
  show (MkPParam l (Explicit, n) t) = "(" ++ show n ++ " : " ++ show t ++ ")"
  show (MkPParam l (Implicit, n) t) = "{" ++ show n ++ " : " ++ show t ++ "}"

public export covering
Show PTel where
  show (MkPTel []) = ""
  show (MkPTel ts) = " " ++ (map show ts |> cast |> joinBy " ")

isAtomic : PTm -> Bool
isAtomic (PName _) = True
isAtomic (PLoc _ t) = isAtomic t
isAtomic _ = False

covering
showAtomic : PTm -> String

public export covering
Show PTm where
  show (PName n) = show n
  show t@(PLam _ _ _) = let (args, ret) = pGatherLams t in "\\" ++ joinBy " " (map (\((md, n), ty) => case ty of
        Nothing => case md of
          Explicit => show n
          Implicit => "{" ++ show n ++ "}"
        Just ty => show (MkPParam dummyLoc (md, n) ty)
      ) args) ++ " => " ++ show ret
  show t@(PApp _ _) = let (s, sp) = pGatherApps t in showAtomic s ++ " " ++ joinBy " " (cast $ map showAtomic sp)
  show (PPi (MkPParam _ (Explicit, "_") a) b) = showAtomic a ++ " -> " ++ show b
  show (PPi p b) = show p ++ " -> " ++ show b
  show (PSigma (MkPParam _ (Explicit, "_") a) b) = showAtomic a ++ " ** " ++ show b
  show (PSigma p b) = show p ++ " ** " ++ show b
  show (PLet n Nothing v t) = "let " ++ show n ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show (PLoc _ t) = show t

showAtomic t = if isAtomic t then show t else "(" ++ show t ++ ")"
