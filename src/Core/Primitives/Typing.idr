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
obj bx x = MkAnnot x (PrimType $> [(Val _, PrimSta $> [(Val _, bx)])]) Obj

objZ : Size ns => Atom ns -> Annot ns
objZ x = obj (PrimZeroLayout $> []) x

-- objSizedTy : Atom ns -> Annot ns
-- objSizedTy = ?fafa

-- Typing rules for all the primitives
public export covering
primAnnot : Size ns => (p : Primitive k r ar) -> (Tel ar Annot ns, Annot (ns ::< ar))
primAnnot PrimTYPE = ([], mta (PrimTYPE $> []))

primAnnot PrimCode = ([
      (Val (_, "bytes"), mta (PrimLayoutDyn $> [])),
      (Val _, objZ (PrimType $> [(Val _, v "bytes")]))
    ],
    mta (PrimTYPE $> [])
  )
primAnnot PrimQuote = ([
      (Val (_, "bytes"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bytes")])])),
      (Val _, obj (v "bytes") (v "ty"))
    ],
    mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "bytes")]), (Val _, v "ty")])
  )
primAnnot PrimSplice = ([
      (Val (_, "bytes"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bytes")])])),
      (Val _, mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "bytes")]), (Val _, v "ty")]))
    ],
    obj (v "bytes") (v "ty")
  )
primAnnot PrimSta = ([(Val _, mta (PrimLayout $> []))], mta (PrimLayoutDyn $> []))
primAnnot PrimType = ([(Val (_, "bs"), mta (PrimLayoutDyn $> []))], objZ (PrimType $> [(Val _, PrimZeroLayout $> [])]))
primAnnot PrimSeqLayout = ([
      (Val _, mta (PrimLayout $> [])),
      (Val _, mta (PrimLayout $> []))
    ],
    mta (PrimLayout $> [])
  )
primAnnot PrimSeqLayoutDyn = ([
      (Val _, mta (PrimLayoutDyn $> [])),
      (Val _, mta (PrimLayoutDyn $> []))
    ],
    mta (PrimLayoutDyn $> [])
  )
primAnnot PrimLayout = ([], mta (PrimTYPE $> []))
primAnnot PrimZeroLayout = ([], mta (PrimLayout $> []))
primAnnot PrimIdxLayout = ([], mta (PrimLayout $> []))
primAnnot PrimPtrLayout = ([], mta (PrimLayout $> []))
primAnnot PrimLayoutDyn = ([], mta (PrimTYPE $> []))
primAnnot PrimMake = ([
      (Val (_, "bytes"), mta (PrimLayoutDyn $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, v "bytes")]))
    ],
    objZ (PrimType $> [(Val _, PrimSta $> [(Val _, PrimIdxLayout $> [])])])
  )
primAnnot PrimGive = ([
      (Val (_, "bytes"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bytes")])])),
      (Val _, obj (v "bytes") (v "ty"))
    ],
    obj (PrimIdxLayout $> []) (PrimMake $> [(Val _, v "bytes"), (Val _, v "ty")])
  )
primAnnot PrimPush = ([
      (Val (_, "bytes"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bytes")])])),
      (Val _, obj (PrimIdxLayout $> []) (PrimMake $> [(Val _, v "bytes"), (Val _, v "ty")]))
    ],
    obj (v "bytes") (v "ty")
  )
primAnnot PrimUNIT = ([], mta (PrimTYPE $> []))
primAnnot PrimTT = ([], mta (PrimUNIT $> []))
primAnnot PrimIrrTy = ([
      (Val (_, "bytes"), mta (PrimLayoutDyn $> [])),
      (Val _, objZ (PrimType $> [(Val _, v "bytes")]))
    ],
    objZ (PrimType $> [(Val _, PrimSta $> [(Val _, PrimZeroLayout $> [])])])
  )
primAnnot PrimIrr = ([
      (Val (_, "bytes"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bytes")])])),
      (Val _, obj (v "bytes") (v "ty"))
    ], 
    objZ (PrimIrrTy $> [(Val _, v "bytes"), (Val _, v "ty")])
  )
primAnnot PrimUnit = ([(Val _, mta (PrimLayoutDyn $> []))], objZ (PrimType $> [(Val _, v "bytes")]))
primAnnot PrimTt = ([
      (Val _, mta (PrimLayoutDyn $> []))
    ],
    obj (PrimIdxLayout $> []) (PrimMake $> [(Val _, v "bytes"), (Val _, PrimUnit $> [(Val _, v "bytes")])])
  )
primAnnot (PrimSIGMA a) = ([
      (Val (_, snd a), mta (PrimTYPE $> [])),
      (Val _, mta (mtaPi a (v (snd a)) (PrimTYPE $> [])))
    ],
    mta (PrimTYPE $> [])
  )
primAnnot (PrimPAIR a) = ([
      (Val (_, snd a), mta (PrimTYPE $> [])),
      (Val (_, "rest"), mta (mtaPi a (v (snd a)) (PrimTYPE $> []))),
      (Val (_, "va"), mta (v (snd a))),
      (Val _, mta (app (v "rest") (Explicit, "x") (v "va")))
    ],
    mta (mtaSigma a (v (snd a)) (v "rest"))
  )
primAnnot PrimIOTy = ([
  (Val (_, "bt"), mta (PrimLayout $> [])),
  (Val _, objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bt")])]))
    ],
    objZ (PrimType $> [(Val _, PrimPtrLayout $> [])])
  )
primAnnot PrimIOBind = ([
      (Val (_, "ba"), mta (PrimLayout $> [])),
      (Val (_, "bb"), mta (PrimLayout $> [])),
      (Val (_, "a"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "ba")])])),
      (Val (_, "b"), objZ (PrimType $> [(Val _, PrimSta $> [(Val _, v "bb")])])),
      (Val _, obj (PrimPtrLayout $> []) (PrimIOTy $> [(Val _, v "ba"), (Val _, v "a")])),
      (?Fajj)
    ],
    obj (PrimPtrLayout $> []) (PrimIOTy $> [(Val _, v "bb"), (Val _, v "b")])
  )
primAnnot PrimIORet = ?primioret
-- primAnnot (PrimSigma a) = ([
--   (Val _, layoutDynAnnot.p),
--   (Val _, layoutDynAnnot.p),
--   (Val _, (dynObjTypeAnnot (v "ba")).p),
--   (Val _, (mtaPi (Explicit, "x")
--     ((code (v "ba") (v a)).ty)
--     (code (prim PrimSta [(Val _, (prim PrimZeroLayout []).tm)]).tm (dynObjTypeAnnot (v "bRest")).ty).ty).toAnnot.p)
--   ], (dynObjTypeAnnot (prim PrimSeqLayoutDyn [(Val _, v "ba"), (Val _, v "bRest")]).tm).p)
-- primAnnot (PrimPair a) = ([
--   (Val _, layoutDynAnnot.p),
--   (Val _, layoutDynAnnot.p),
--   (Val _, (dynObjTypeAnnot (v "ba")).p),
--   (Val _, (mtaPi (Explicit, "x")
--     ((code (v "ba") (v a)).ty)
--     (code (prim PrimSta [(Val _, (prim PrimZeroLayout []).tm)]).tm (dynObjTypeAnnot (v "bRest")).ty).ty).toAnnot.p),
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