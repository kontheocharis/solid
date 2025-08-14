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
import Core.Metavariables
import Core.Typechecking
import Core.Primitives.Definitions
import Core.Primitives.Rules
import Surface.Presyntax
import Core.Syntax
import Data.Maybe
import Control.Monad.State

public export
interface HasTc m => HasElab m where

-- Elaborate a presyntax term into a typechecking operation.
export covering
elab : (HasElab m) => PTm -> TcAll m

-- The annotation of the entry point of the program
export
mainAnnot : AnnotAt Obj [<]
-- mainAnnot = (ioTy (unitTy Obj)).a

-- export
-- runElab : (HasElab m) => Elab m a -> m a
-- runElab = evalStateT (MkElabState Nothing)

covering
elabSpine : (HasElab m) => PSpine k -> List (Ident, TcAll m)
elabSpine (MkPSpine []) = []
elabSpine (MkPSpine (MkPArg l n v :: xs)) = (
    fromMaybe (Explicit, "_") n,
    interceptAll (enterLoc l) $ elab v
  ) :: elabSpine (MkPSpine xs)

elab (PLoc l t) = interceptAll (enterLoc l) $ elab t
elab (PName n) = tcVar n
elab (PLam (MkPTel []) t) = elab t
elab (PLam (MkPTel ((MkPParam l n ty) :: xs)) t) =
  let t' = elab {m = m} (PLam (MkPTel xs) t) in
  let ty = elab <$> ty in
  tcLam n (interceptAll (enterLoc l) <$> ty) t'
elab (PPi (MkPTel []) t) = elab t
elab (PPi (MkPTel ((MkPParam l n ty) :: xs)) t) =
  let t' = elab {m = m} (PPi (MkPTel xs) t) in
  let ty' = fromMaybe (PHole Nothing) ty in
  let ty = elab ty' in
  tcPi n (interceptAll {m = m} (enterLoc l) ty) t'
elab (PApp subject sp) = tcApps (elab subject) (elabSpine sp)
elab (PHole n) = tcHole n
elab PUnit = switch $ \ctx, maybeStage => do
  ?fajajj
elab (PSigmas (MkPTel [])) = elab PUnit
elab (PSigmas (MkPTel ((MkPParam l n ty) :: xs))) =
  let t' = elab {m = m} (PSigmas (MkPTel xs)) in
  let ty' = fromMaybe (PHole Nothing) ty in
  ?tcSigma n (interceptAll {m = m} (enterLoc l) (elab ty')) t'
elab (PPairs ps) = ?tcPairs -- <$> elabSpine ps
elab (PProj v n) = ?tcProj -- !(elab v) n
elab (PBlock t []) = elab PUnit
elab (PBlock t (PLet l n ty tm :: bs)) =
  let ty' = elab <$> ty in
  let statement = tcLet n ?stage ty' (elab tm) (elab (PBlock t bs)) in
  interceptAll (enterLoc l) statement
elab (PBlock t (PLetRec l n ty tm :: bs)) =
  let statement = tcLetRec n ?stage2 (elab ty) (elab tm) (elab (PBlock t bs)) in
  interceptAll (enterLoc l) statement
elab (PBlock t (PBlockTm l tm :: [])) = elab tm
elab (PBlock t (PDecl l n ty :: bs)) = ?todoDecl
elab (PBlock t (PLet l n ty tm :: bs)) = ?todoIrrLet
elab (PBlock t (PLetRec l n ty tm :: bs)) = ?todoIrrLetRec
elab (PBlock t (PBind l n ty tm :: bs)) = ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) = ?todoNamelessBind
elab (PBlock t (PDirSt d b :: bs)) = elab (PBlock t (b :: bs)) -- @@TODO
elab (PLit l) = ?todoLit
elab (PDirTm d t) = elab t -- @@TODO
