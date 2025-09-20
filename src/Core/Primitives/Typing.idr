-- Typing rules for the core primitives.
-- Relies on the "Atoms" module.
module Core.Primitives.Typing

import Data.DPair
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Metavariables
import Core.Unification
import Core.Primitives.Rules
import Core.Atoms
import Core.Combinators
import Core.Context

arg : {n : _} -> Expr ns -> (Singleton n, Annot ns)
arg e = (Val _, e.a)

argN : {m : _} -> (n : String) -> Expr ns -> (Singleton (m, n), Annot ns)
argN _ e = (Val _, e.a)

ret : Expr ns -> Annot ns
ret = (.a)

-- Typing rules for all the *native* primitives
-- 
-- Typing for the rest of the primitives is given in the prelude.
public export covering
primAnnot : Size ns => (p : Primitive k r PrimNative ar) -> Op ar ns
primAnnot PrimTYPE = ([], ret $ mta (PrimTYPE $> []))
primAnnot PrimCode = ([
      argN "l" $ mta (PrimLayoutDyn $> []),
      arg $ objZ (PrimTypeDyn $> [(Val _, v "l")])
    ],
    ret $ mta (PrimTYPE $> [])
  )
primAnnot PrimQuote = ([
      argN "l" $ mta (PrimLayout $> []),
      argN "ty" $ objZ (PrimTypeSta $> [(Val _, v "l")]),
      arg $ obj (v "l") (v "ty")
    ],
    ret $ mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")])
  )
primAnnot PrimSplice = ([
      argN "l" $ mta (PrimLayout $> []),
      argN "ty" $ objZ (PrimTypeSta $> [(Val _, v "l")]),
      arg $ mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")])
    ],
    ret $ obj (v "l") (v "ty")
  )
primAnnot PrimSta = ([arg $ mta (PrimLayout $> [])], ret $ mta (PrimLayoutDyn $> []))
primAnnot PrimTypeDyn = ([
      arg $ mta (PrimLayoutDyn $> [])
    ],
    ret $ objZ (PrimTypeSta $> [(Val _, PrimZeroLayout $> [])])
  )
primAnnot PrimTypeSta = ([
      arg $ mta (PrimLayout $> [])
    ],
    ret $ objZ (PrimTypeSta $> [(Val _, PrimZeroLayout $> [])])
  )
primAnnot PrimSeqLayout = ([
      arg $ mta (PrimLayout $> []),
      arg $ mta (PrimLayout $> [])
    ],
    ret $ mta (PrimLayout $> [])
  )
primAnnot PrimSeqLayoutDyn = ([
      arg $ mta (PrimLayoutDyn $> []),
      arg $ mta (PrimLayoutDyn $> [])
    ],
    ret $ mta (PrimLayoutDyn $> [])
  )
primAnnot PrimLayout = ([], ret $ mta (PrimTYPE $> []))
primAnnot PrimZeroLayout = ([], ret $ mta (PrimLayout $> []))
primAnnot PrimIdxLayout = ([], ret $ mta (PrimLayout $> []))
primAnnot PrimPtrLayout = ([], ret $ mta (PrimLayout $> []))
primAnnot PrimLayoutDyn = ([], ret $ mta (PrimTYPE $> []))
primAnnot PrimUNIT = ([], ret $ mta (PrimTYPE $> []))
primAnnot PrimTT = ([], ret $ mta (PrimUNIT $> []))
primAnnot PrimUnit = ([], ret $ objZ (PrimTypeSta $> [(Val _, PrimZeroLayout $> [])]))
primAnnot PrimTt = ([], ret $ objZ (PrimUnit $> []))
primAnnot PrimFix = ([
      argN "l" $ mta (PrimLayout $> []),
      argN "A" $ objZ (PrimTypeSta $> [(Val _, v "l")]),
      argN "a" $
        (pi Obj (Explicit, "x")
          (MkAnnotFor (ObjSort Sized (v "l")) (v "A"))
          (MkAnnotFor (ObjSort Sized (v "l")) (close idS $ v "A"))).p
    ],
    ret $ obj (v "l") (v "A")
  )
primAnnot PrimFIX = ([
      argN "A" $ objZ (PrimTYPE $> []),
      argN "a" $
        (pi Mta (Explicit, "x")
          (MkAnnotFor MtaSort (v "A"))
          (MkAnnotFor MtaSort (close idS $ v "A"))).p
    ],
    ret $ mta (v "A")
  )

-- The argument types for the given primitive
public export covering
0 PrimArgs : Primitive k r n ar -> (Ctx -> Type) -> Ctx -> Type
PrimArgs _ tm = Spine ar tm

-- Create a primitive expression with the given data.
public export covering
prim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility}
  -> Primitive k r l ar
  -> Spine ar Atom ns
  -> Annot (ns ::< ar)
  -> Expr ns
prim @{s} p sp pRet =
  let ret = sub {sms = s + sp.count} (idS ::< sp) pRet.ty in
  let retSort = sub {sms = s + sp.count} (idS ::< sp) pRet.sort in
  MkExpr (Choice (sPrim p sp.syn) (vPrim p sp.val)) (MkAnnot ret retSort pRet.stage)

public export covering
code : Size ns => AnnotFor Obj k Atom ns -> AnnotAt Mta ns
code (MkAnnotFor so ty) = PrimCode $> [(Val _, (sortBytes so)), (Val _, ty)] `asTypeIn` mtaA.f

public export covering
quot : Size ns => ExprFor Obj k ns -> ExprAt Mta ns
quot (MkExpr tm ann@(MkAnnotFor so ty)) =
  MkExpr (PrimQuote $> [(Val _, sortBytes so), (Val _, ty), (Val _, tm)]) (code ann)

public export covering
splice : Size ns => AnnotFor Obj k Atom ns -> Atom ns -> ExprAt Obj ns
splice uncoded@(MkAnnotFor so ty) tm = MkExpr (PrimSplice $> [(Val _, (sortBytes so)), (Val _, ty), (Val _, tm)]) uncoded.asAnnot
  
public export
data ForceTo : (tm : Ctx -> Type) -> (info : Ctx -> Type) -> Ctx -> Type where
  Matching : forall tm . info ns -> ForceTo tm info ns
  NonMatching : forall tm . tm ns -> ForceTo tm info ns
  
public export covering
forceCode : HasMetas m => Context bs ns
  -> (potentialCode : Atom ns)
  -> m SolvingAllowed (ForceTo Atom (PrimArgs PrimCode Atom) ns)
forceCode ctx potentialCode = matchOnNf ctx.scope potentialCode >>= \s => case s.val of
  SimpPrimNormal (SimpApplied PrimCode sp) => pure $ Matching (promoteSpine sp)
  got => do
    by <- freshMeta ctx Nothing layoutA.f
    ty <- freshMeta ctx Nothing objZA.f
    let exp = code @{ctxSize ctx} (MkAnnotFor (ObjSort Dyn by.tm) ty.tm)
    unify ctx.scope got exp.ty.val >>= \case
      AreSame => pure $ Matching [(Val _, by.tm), (Val _, ty.tm)]
      _ => pure $ NonMatching (promote got)
    