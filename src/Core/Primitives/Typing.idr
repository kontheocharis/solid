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


public export covering
($>) : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility}
    -> Primitive k r ar
    -> Spine ar Atom ns
    -> Atom ns
($>) p sp = ?ffa -- promote $ SynPrimNormal x

mta : Size ns => Atom ns -> Annot ns
mta x = MkAnnot x (PrimTYPE $> []) Mta

obj : Size ns => Atom ns -> Atom ns -> Annot ns
obj bx x = MkAnnot x (PrimType $> [(Val _, bx)]) Obj

-- objSizedTy : Atom ns -> Annot ns
-- objSizedTy = ?fafa

-- Typing rules for all the primitives
public export covering
primAnnot : Size ns => (p : Primitive k r ar) -> (Tel ar Annot ns, Annot (ns ::< ar))
primAnnot PrimTYPE = ([], mta (PrimTYPE $> []))

primAnnot PrimCode = ([
      (Val _, mta (PrimLayoutDyn $> [])),
      (Val _, obj (PrimZeroLayout $> []) (PrimType $> [(Val _, v "bytes")]))
    ],
    mta (PrimTYPE $> [])
  )
primAnnot PrimQuote = ([
      (Val _, layoutDynAnnot.p),
      (Val _, (dynObjTypeAnnot (v "bytes")).p),
      (Val _, ((v "ty") `asTypeIn` dynObjTypeAnnot (v "bytes")).p)
    ],
    (code (v "bytes") (v "ty")).p
  )
primAnnot PrimSplice = ([
      (Val _, layoutDynAnnot.p),
      (Val _, (dynObjTypeAnnot (v "bytes")).p),
      (Val _, (code (v "bytes") (v "ty")).p)
    ],
    (v "ty" `asTypeIn` dynObjTypeAnnot (v "bytes")).p
  )
primAnnot PrimLayout = ([], mtaTypeAnnot.p)
primAnnot PrimZeroLayout = ([], layoutAnnot.p)
primAnnot PrimIdxLayout = ([], layoutAnnot.p)
primAnnot PrimPtrLayout = ([], layoutAnnot.p)
primAnnot PrimLayoutDyn = ([], (sizedObjTypeAnnot (promote idxLayout)).p)
primAnnot PrimUNIT = ([], mtaTypeAnnot.p)
primAnnot PrimTT = ([], (unitTy Mta).toAnnot.p)
primAnnot PrimIrrTy = ([
      (Val _, layoutDynAnnot.p),
      (Val _, (sizedObjTypeAnnot (v "bytes")).p)
    ],
    (sizedObjTypeAnnot (promote zeroLayout)).p
  )
primAnnot PrimIrr = ([
      (Val _, layoutDynAnnot.p),
      (Val _, (sizedObjTypeAnnot (v "bytes")).p),
      (Val _, ((v "ty") `asTypeIn` dynObjTypeAnnot (v "bytes")).p)
    ], 
    (irrTy (v "bytes") (v "ty")).p.toAnnot
  )
primAnnot PrimUnit = ([(Val _, layoutDynAnnot.p)], (sizedObjTypeAnnot (v "bytes")).p)
primAnnot PrimTt = ([(Val _, layoutDynAnnot.p)], (objUnitTy (v "bytes")).p.toAnnot)
primAnnot PrimStaLayoutDyn = ([(Val _, mtaTypeAnnot.p)], layoutDynAnnot.p)
primAnnot PrimType = ([(Val _, layoutDynAnnot.p)], (sizedObjTypeAnnot (promote zeroLayout)).p)
primAnnot PrimSeqLayout = ([(Val _, layoutAnnot.p), (Val _, layoutAnnot.p)], layoutAnnot.p)
primAnnot PrimSeqLayoutDyn = ([(Val _, layoutDynAnnot.p), (Val _, layoutDynAnnot.p)], layoutDynAnnot.p)
primAnnot (PrimSIGMA a) = ([
      (Val _, mtaTypeAnnot.p),
      (Val _, (mtaPi a (v (snd a)) mtaTypeAnnot.ty).toAnnot.p)
    ],
    mtaTypeAnnot.p
  )
primAnnot (PrimPAIR a) = ([
  (Val _, mtaTypeAnnot.p),
  (Val _, (mtaPi (Explicit, "x") (v (snd a)) mtaTypeAnnot.ty).toAnnot.p),
  (Val _, (v (snd a) `asTypeIn` mtaTypeAnnot).p),
  (Val _, (app (v "rest") (Explicit, "x") (v "va") `asTypeIn` mtaTypeAnnot).p)
  ], (mtaSigma a (v (snd a)) (v "rest")).toAnnot.p)
primAnnot PrimIOTy = ([
      (Val _, layoutAnnot.p),
      (Val _, (sizedObjTypeAnnot (v "bt")).p)
    ],
    (sizedObjTypeAnnot (promote ptrLayout)).p
  )
primAnnot PrimIOBind = ?primAnnot_missing_case_2
primAnnot PrimIORet = ?primAnnot_missing_case_3
-- primAnnot (PrimSigma a) = ([
--   (Val _, layoutDynAnnot.p),
--   (Val _, layoutDynAnnot.p),
--   (Val _, (dynObjTypeAnnot (v "ba")).p),
--   (Val _, (mtaPi (Explicit, "x")
--     ((code (v "ba") (v a)).ty)
--     (code (prim PrimStaLayoutDyn [(Val _, (prim PrimZeroLayout []).tm)]).tm (dynObjTypeAnnot (v "bRest")).ty).ty).toAnnot.p)
--   ], (dynObjTypeAnnot (prim PrimSeqLayoutDyn [(Val _, v "ba"), (Val _, v "bRest")]).tm).p)
-- primAnnot (PrimPair a) = ([
--   (Val _, layoutDynAnnot.p),
--   (Val _, layoutDynAnnot.p),
--   (Val _, (dynObjTypeAnnot (v "ba")).p),
--   (Val _, (mtaPi (Explicit, "x")
--     ((code (v "ba") (v a)).ty)
--     (code (prim PrimStaLayoutDyn [(Val _, (prim PrimZeroLayout []).tm)]).tm (dynObjTypeAnnot (v "bRest")).ty).ty).toAnnot.p),
--   (Val _, (v a `asTypeIn` dynObjTypeAnnot (v "ba")).p),
--   (Val _, (app (v "rest") (v "va") `asTypeIn` ?fjjjjjj).p)
--   ], (prim (PrimSigma a) [(Val _, v "ba"), (Val _, v "bRest"), (Val _, v a), (Val _, v "rest")]).toAnnot)

-- Create a primitive expression with the given data.
public export covering
prim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility} -> Primitive k r ar -> Spine ar Atom ns -> Expr ns
prim @{s} p sp =
  let (_, pRet) = primAnnot {ns = ns} p in
  let ret = sub {sms = s + sp.count} (idS ::< sp) pRet.ty in
  let retSort = sub {sms = s + sp.count} (idS ::< sp) pRet.sort in
  ?fajajj
  -- MkExpr (Choice (sPrim p sp.syn) (vPrim p sp.val)) (MkAnnot ret retSort pRet.stage)