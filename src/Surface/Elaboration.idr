-- Elaboration of surface syntax to typechecking operations.
--
-- These can be run in an existing context to produce a core term.
module Surface.Elaboration

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Core.Base
import Core.Atoms
import Core.Combinators
import Core.Typechecking
import Core.Primitives.Definitions
import Core.Primitives.Rules
import Surface.Presyntax
import Core.Syntax
import Data.Maybe

-- Elaborate a presyntax term into a typechecking operation.
export covering
elab : (HasTc m) => PTm -> TcAll m

-- The annotation of the entry point of the program
export
mainAnnot : AnnotAt Obj [<]
mainAnnot = (ioTy (unitTy Obj)).a

covering
elabSpine : (HasTc m) => PSpine k -> List (Ident, TcAll m)
elabSpine (MkPSpine []) = []
elabSpine (MkPSpine (MkPArg l n v :: xs))
  = (fromMaybe (Explicit, "_") n, interceptAll (enterLoc l) $ elab v) :: elabSpine (MkPSpine xs)

elab (PLoc l t) = interceptAll (enterLoc l) $ elab t
elab (PName n) = tcVar n
elab (PLam (MkPTel []) t) = elab t
elab (PLam (MkPTel ((MkPParam l n ty) :: xs)) t)
  = let t' = elab {m = m} (PLam (MkPTel xs) t) in
    tcLam n (interceptAll (enterLoc l) <$> (elab <$> ty)) t'
elab (PPi (MkPTel []) t) = elab t
elab (PPi (MkPTel ((MkPParam l n ty) :: xs)) t)
  = let t' = elab {m = m} (PPi (MkPTel xs) t) in
    let ty' = fromMaybe (PHole Nothing) ty in
    tcPi n (interceptAll {m = m} (enterLoc l) $ elab ty') t'
elab (PApp subject sp) = tcApp (elab subject) (elabSpine sp)
elab (PHole n) = tcHole n
elab PUnit = tcUnit
elab (PSigmas (MkPTel [])) = elab PUnit
elab (PSigmas (MkPTel ((MkPParam l n ty) :: xs)))
  = let t' = elab {m = m} (PSigmas (MkPTel xs)) in
    let ty' = fromMaybe (PHole Nothing) ty in
    tcSigma n (interceptAll {m = m} (enterLoc l) $ elab ty') t'
elab (PPairs ps) = tcPairs (elabSpine ps)
elab (PProj v n) = tcProj (elab v) n
elab (PBlock t []) = tcUnit
elab (PBlock t (PLet l (MkLetFlags stage False) n ty tm :: bs))
  = let statement = tcLet n stage (elab <$> ty) (elab tm) (elab (PBlock t bs)) in
    interceptAll (enterLoc l) statement
elab (PBlock t (PLetRec l (MkLetFlags stage False) n ty tm :: bs))
  = let statement = tcLetRec n stage (elab ty) (elab tm) (elab (PBlock t bs)) in
    interceptAll (enterLoc l) statement
elab (PBlock t (PBlockTm l tm :: [])) = elab tm
elab (PBlock t (PDecl l n ty :: bs)) = ?todoDecl
elab (PBlock t (PLet l (MkLetFlags stage True) n ty tm :: bs)) = ?todoIrrLet
elab (PBlock t (PLetRec l (MkLetFlags stage True) n ty tm :: bs)) = ?todoIrrLetRec
elab (PBlock t (PBind l n ty tm :: bs)) = ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) = ?todoNamelessBind
elab (PLit l) = ?todoLit
