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
obj bx x = MkAnnot x (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, bx)])]) Obj

objZ : Size ns => Atom ns -> Annot ns
objZ x = obj (PrimZeroLayout $> []) x

-- Typing rules for all the primitives
public export covering
primAnnot : Size ns => (p : Primitive k r ar) -> (Tel ar Annot ns, Annot (ns ::< ar))
primAnnot PrimTYPE = ([], mta (PrimTYPE $> []))
primAnnot PrimCode = ([
      (Val (_, "l"), mta (PrimLayoutDyn $> [])),
      (Val _, objZ (PrimTypeDyn $> [(Val _, v "l")]))
    ],
    mta (PrimTYPE $> [])
  )
primAnnot PrimQuote = ([
      (Val (_, "l"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, v "l")])])),
      (Val _, obj (v "l") (v "ty"))
    ],
    mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")])
  )
primAnnot PrimSplice = ([
      (Val (_, "l"), mta (PrimLayout $> [])),
      (Val (_, "ty"), objZ (PrimTypeDyn $> [(Val _, PrimSta $> [(Val _, v "l")])])),
      (Val _, mta (PrimCode $> [(Val _, PrimSta $> [(Val _, v "l")]), (Val _, v "ty")]))
    ],
    obj (v "l") (v "ty")
  )
primAnnot PrimSta = ([(Val _, mta (PrimLayout $> []))], mta (PrimLayoutDyn $> []))
primAnnot PrimTypeDyn = ([(Val (_, "l"), mta (PrimLayoutDyn $> []))], objZ (PrimTypeDyn $> [(Val _, PrimZeroLayout $> [])]))
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

-- Create a primitive expression with the given data.
public export covering
prim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility} -> Primitive k r ar -> Spine ar Atom ns -> Expr ns
prim @{s} p sp =
  let (_, pRet) = primAnnot {ns = ns} p in
  let ret = sub {sms = s + sp.count} (idS ::< sp) pRet.ty in
  let retSort = sub {sms = s + sp.count} (idS ::< sp) pRet.sort in
  ?fajajj
  -- MkExpr (Choice (sPrim p sp.syn) (vPrim p sp.val)) (MkAnnot ret retSort pRet.stage)