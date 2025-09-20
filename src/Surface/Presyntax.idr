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
PTy : Type
PTy = PTm

public export
PPat : Type
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

-- -- Varius flags for let statements
-- public export
-- record LetFlags where
--   constructor MkLetFlags
--   -- Which stage to bind the let in
--   stage : Maybe Stage
--   -- Whether the RHS is irrelevant, and if so we can extract its value as long
--   -- as the rest of the block is zero-sized.
--   irr : Bool

-- public export
-- letFlagsAreDefault : LetFlags -> Bool
-- letFlagsAreDefault (MkLetFlags Nothing False) = True
-- letFlagsAreDefault _ = False

-- Binary operators
--
-- @@Todo: Actually use this
public export
data BinOp = Times | Plus
           
-- Directives
-- For now just strings
public export
record Directive where
  constructor MkDirective
  name : String
  
-- All known directives
public export
data KnownDirective : Type where
  MtaDir : KnownDirective 
  ObjDir : KnownDirective 
  PrimitiveDir : KnownDirective
  DebugCtx : KnownDirective
  DebugTerm : KnownDirective
  DebugTermExp : KnownDirective
  DebugType : KnownDirective
  DebugTypeExp : KnownDirective
  Import : KnownDirective
  
export
fromStage : Stage -> KnownDirective
fromStage Obj = ObjDir
fromStage Mta = MtaDir
  
export covering
(.asDirective) : KnownDirective -> Directive
(.asDirective) MtaDir = MkDirective "mta"
(.asDirective) ObjDir = MkDirective "obj"
(.asDirective) PrimitiveDir = MkDirective "primitive"
(.asDirective) DebugCtx = MkDirective "debug-ctx"
(.asDirective) DebugTerm = MkDirective "debug-term"
(.asDirective) DebugTermExp = MkDirective "debug-term-exp"
(.asDirective) DebugType = MkDirective "debug-type"
(.asDirective) DebugTypeExp = MkDirective "debug-type-exp"
(.asDirective) Import = MkDirective "import"
  
export covering
parseDirective : Directive -> Maybe KnownDirective
parseDirective (MkDirective "mta") = Just MtaDir
parseDirective (MkDirective "obj") = Just ObjDir
parseDirective (MkDirective "primitive") = Just PrimitiveDir
parseDirective (MkDirective "debug-ctx") = Just DebugCtx
parseDirective (MkDirective "debug-term") = Just DebugTerm
parseDirective (MkDirective "debug-term-exp") = Just DebugTermExp
parseDirective (MkDirective "debug-type") = Just DebugType
parseDirective (MkDirective "debug-type-exp") = Just DebugTypeExp
parseDirective (MkDirective "import") = Just Import
parseDirective _ = Nothing

export covering
directiveCoh : {k : _} -> parseDirective k.asDirective = Just k
directiveCoh {k = MtaDir} = Refl
directiveCoh {k = ObjDir} = Refl
directiveCoh {k = PrimitiveDir} = Refl
directiveCoh {k = DebugCtx} = Refl
directiveCoh {k = DebugTerm} = Refl
directiveCoh {k = DebugTermExp} = Refl
directiveCoh {k = DebugType} = Refl
directiveCoh {k = DebugTypeExp} = Refl
directiveCoh {k = Import} = Refl

-- A block is a sequence of assignment-like things. It is written like
-- { x1 := a1; ... ; xn := an; y }, similar to Rust.
public export
data PBlockStatement : Type where
  -- Directive-wrapped statement
  PDirSt : Directive -> PBlockStatement -> PBlockStatement
  -- Recursive let statement
  --
  -- x : A
  -- x = a
  PLetRec : Loc -> (name : String) -> PTy -> PTm -> PBlockStatement
  -- Declaration without an assignment
  --
  -- x : A
  PDecl : Loc -> (name : String) -> PTy -> PBlockStatement
  -- Let statement
  --
  -- x : A = a
  -- or
  -- x := a
  PLet : Loc -> (name : String) -> Maybe PTy -> PTm -> PBlockStatement
  -- Monadic bind statement
  --
  -- x : A <- a
  -- or
  -- x <- a
  PBind : Loc -> (name : String) -> Maybe PTy -> PTm -> PBlockStatement
  -- Just a term statement; monadic or returning a value
  --
  -- a
  PBlockTm : Loc -> PTm -> PBlockStatement

-- Handy wrapper for top-level statements
public export
record PBlockStatements where
  constructor MkPBlockStatements
  inner : List PBlockStatement

-- Goal is a context and an expected type
public export
record PGoal where
  constructor MkPGoal
  ctx : PBlockStatements
  holeStage : Stage
  holeTm : PTm
  holeTy : PTy

-- Main syntax tree, pretty self explanatory
--
-- All the binders have a gathered list of parameters.
public export
data PTm : Type where
  PName : String -> PTm
  PLam : PTel Functions -> PTm -> PTm
  PApp : PTm -> PSpine Functions -> PTm
  PPi : PTel Functions -> PTy -> PTy
  -- Directives
  PDirTm : Directive -> PTm -> PTm
  -- This stands for both types and terms
  PUnit : PTm
  -- If there is a single element these are elaborated to their contents.
  -- If there are none, it is the unit.
  -- Otherwise it is an iterated pair type.
  PSigmas : PTel Pairs -> PTy
  PPairs : PSpine Pairs -> PTm
  PHole : (name : Maybe String) -> PTy
  PBlock : (topLevel : Bool) -> List PBlockStatement -> PTm
  -- Projection e.g. x.n : A where x : (.., n : A, ...)
  PProj : PTm -> (field : String) -> PTm
  PLoc : Loc -> PTm -> PTm
  PLit : Lit -> PTm

public export
Show PTm

export
pGatherLams : PTm -> (PTel Functions, PTm)
pGatherLams (PLam (MkPTel xs) y)
  = let (MkPTel xs', z) = pGatherLams y in (MkPTel (xs ++ xs'), z)
pGatherLams (PLoc x y) = pGatherLams y
pGatherLams (PApp x (MkPSpine [])) = pGatherLams x
pGatherLams x = (MkPTel [], x)

-- Smart constructors for binders and spined terms
export
pLam : PParam Functions -> PTm -> PTm
pLam p (PLam (MkPTel ps) y) = PLam (MkPTel (p :: ps)) y
pLam p t = PLam (MkPTel [p]) t

export
pPi : PParam Functions -> PTy -> PTy
pPi p (PPi (MkPTel ps) y) = PPi (MkPTel (p :: ps)) y
pPi p t = PPi (MkPTel [p]) t

export
pApp : PTm -> PArg Functions -> PTm
pApp (PApp s (MkPSpine xs)) a = PApp s (MkPSpine (xs ++ [a]))
pApp s a = PApp s (MkPSpine [a])

export
pApps : PTm -> PSpine Functions -> PTm
pApps (PApp s (MkPSpine sp)) (MkPSpine sp') = PApp s (MkPSpine (sp ++ sp'))
pApps s sp' = PApp s sp'

export
pPair : PArg Pairs -> PArg Pairs -> PTm
pPair a b = PPairs (MkPSpine [a, b])

export
pLet : Loc -> (name : String) -> Maybe PTy -> PTm -> PTm -> PTm
pLet l n ty tm (PBlock t bs) = PBlock t (bs ++ [PLet l n ty tm])
pLet l n ty tm u = PBlock True [PLet l n ty tm, PBlockTm dummyLoc u]

-- Whether the term can always be unambiguously printed without parentheses
public export total
isAtomic : PTm -> Bool
isAtomic (PName _) = True
isAtomic (PApp x (MkPSpine [])) = isAtomic x
isAtomic (PSigmas _) = True
isAtomic PUnit = True
isAtomic (PHole _) = True
isAtomic (PPairs _) = True
isAtomic (PBlock False _) = True
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
  show (MkPArg l (Just (Explicit, "_")) t) = showAtomic t
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
  show (MkPTel [MkPParam l (Explicit, "_") (Just t)]) = showAtomic t
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
  
public export total
Show Directive where
  show (MkDirective n) = "#" ++ n

public export covering
Show PBlockStatement where
  show (PLetRec _ n ty v) = n ++ " : " ++ show ty ++ "\n" ++ n ++ " = " ++ show v
  show (PDecl _ n ty) = n ++ " : " ++ show ty
  show (PLet _ n Nothing v) = n ++ " := " ++ show v
  show (PLet _ n (Just ty) v) = n ++ " : " ++ show ty ++ " = " ++ show v
  show (PBind _ n (Just ty) v) = n ++ " : " ++ show ty ++ " <- " ++ show v
  show (PBind _ n Nothing v) = n ++ " <- " ++ show v
  show (PBlockTm _ t) = show t
  show (PDirSt d s) = show d ++ " " ++ show s

public export covering
Show PBlockStatements where
  show (MkPBlockStatements xs) = map show xs |> joinBy "\n"

public export covering
Show PGoal where
  show (MkPGoal ctx holeStage holeTm holeTy)
    = "\{show ctx}\n------------\n\{show (fromStage holeStage).asDirective} \{show holeTm} : \{show holeTy}"

public export total
Show BinOp where
  show Times = "*"
  show Plus = "+"

public export covering
Show PTm where
  show (PApp x (MkPSpine [])) = show x
  show (PName n) = n
  show l@(PLam _ _) =
    let (args, ret) = pGatherLams l in
     "\\" ++ show args ++ " => " ++ show ret
  show (PApp s sp) = showAtomic s ++ " " ++ show sp
  show (PPi p b) = show p ++ " -> " ++ show b
  show (PSigmas t) = show t
  show (PPairs sp) = show sp
  show (PUnit) = "()"
  show (PBlock True h) = (map show h |> joinBy "\n\n")
  show (PBlock False h) = "{" ++ indented ((map show h |> joinBy ";\n")) ++ "}"
  show (PHole (Just n)) = "?" ++ n
  show (PHole Nothing) = "?"
  show (PProj t n) = showAtomic t ++ "." ++ n
  show (PLoc _ t) = show t
  show (PLit l) = show l
  show (PDirTm d t) = show d ++ " " ++ show t
