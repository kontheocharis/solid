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
      argN "ty" $ objZ (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, v "l")])]),
      arg $ obj (v "l") (v "ty")
    ],
    ret $ mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")])
  )
primAnnot PrimSplice = ([
      argN "l" $ mta (PrimLayout $> []),
      argN "ty" $ objZ (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, v "l")])]),
      arg $ mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")])
    ],
    ret $ obj (v "l") (v "ty")
  )
primAnnot PrimSta = ([arg $ mta (PrimLayout $> [])], ret $ mta (PrimLayoutDyn $> []))
primAnnot PrimTypeDyn = ([
      arg $ mta (PrimLayoutDyn $> [])
    ],
    ret $ objZ (PrimTypeDyn $> [(Val _, PrimZeroLayout $> [])])
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
code : Size ns => AnnotFor Obj k Atom ns -> AnnotFor Mta Static Atom ns
code (MkAnnotFor so ty) =
  MkAnnotFor MtaSort (PrimCode $> [(Val _, (sortBytes so)), (Val _, ty)])

public export covering
quot : Size ns => ExprFor Obj k ns -> ExprFor Mta Static ns
quot (MkExpr tm ann@(MkAnnotFor so ty)) =
  MkExpr (PrimQuote $> [(Val _, sortBytes so), (Val _, ty), (Val _, tm)]) (code ann)

public export covering
splice : Size ns => AnnotFor Obj k Atom ns -> Atom ns -> ExprFor Obj k ns
splice uncoded@(MkAnnotFor so ty) tm =
  MkExpr (PrimSplice $> [(Val _, (sortBytes so)), (Val _, ty), (Val _, tm)]) uncoded
  
data ForceTo : (tm : Ctx -> Type) -> (info : Ctx -> Type) -> Ctx -> Type where
  Matching : forall tm . info ns -> ForceTo tm info ns
  NonMatching : forall tm . tm ns -> ForceTo tm info ns
  
public export covering
forceCode : HasMetas m => Size ns
  => (potentialCode : Atom ns)
  -> {sm : SolvingMode}
  -> m sm (ForceTo Atom (AnnotFor Obj k AtomTy) ns)
forceCode potentialCode = resolve potentialCode >>= \a => case a.val of
  SimpPrimNormal (SimpApplied PrimCode [(Val _, by), (Val _, ty)]) => ?jajjjj
  got => ?fajjaj
    

