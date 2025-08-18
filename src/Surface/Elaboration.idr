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
import Core.Primitives.Typing
import Surface.Presyntax
import Core.Syntax
import Data.Maybe
import Control.Monad.State
import Control.Monad.Error.Either

export
record ElabState where
  constructor MkElabState
  stageHint : Maybe Stage
  
export
data ElabError : Type where
  
export
Show ElabError where
  show t impossible

export
0 Elab : Type -> Type
Elab a = EitherT ElabError (State ElabState) a

export
initialElabState : ElabState
initialElabState = MkElabState Nothing

export
runElab : forall a . Elab a -> Either ElabError a
runElab = evalState initialElabState . runEitherT 

-- Elaborate a presyntax term into a typechecking operation.
export covering
elab : (HasTc m) => PTm -> Elab (TcAll m)

-- The annotation of the entry point of the program
export covering
mainAnnot : AnnotAt Obj [<]
mainAnnot = (objZ (aPrim PrimIO [(Val _, aPrim PrimZeroLayout []), (Val _, aPrim PrimUnit [])])).f.a
 
export
whenInStage : HasTc m => (Maybe Stage -> TcAll m) -> TcAll m
whenInStage f Infer = \ctx, (InferInput maybeStage) => f maybeStage Infer ctx (InferInput maybeStage)
whenInStage f Check = \ctx, (CheckInput stage annot) => f (Just stage) Check ctx (CheckInput stage annot)

covering
elabSpine : (HasTc m) => PSpine k -> Elab (List (Ident, TcAll m))
elabSpine (MkPSpine []) = pure $ []
elabSpine (MkPSpine (MkPArg l n v :: xs)) = pure $ (
    fromMaybe (Explicit, "_") n,
    interceptAll (enterLoc l) $ !(elab v)
  ) :: !(elabSpine (MkPSpine xs))
  
covering
hole : HasTc m => TcAll m
hole = tcHole Nothing

elab (PLoc l t) = pure $ interceptAll (enterLoc l) !(elab t)
elab (PName n) = pure $ tcVar n
elab (PLam (MkPTel []) t) = elab t
elab (PLam (MkPTel ((MkPParam l n ty) :: xs)) t) = do
  t' <- elab {m = m} (PLam (MkPTel xs) t)
  ty <- traverse elab ty
  pure $ tcLam n (interceptAll (enterLoc l) <$> ty) t'
elab (PPi (MkPTel []) t) = elab t
elab (PPi (MkPTel ((MkPParam l n ty) :: xs)) t) = do
  t' <- elab {m = m} (PPi (MkPTel xs) t)
  let ty' = fromMaybe (PHole Nothing) ty
  ty <- elab ty'
  pure $ tcPi n (interceptAll {m = m} (enterLoc l) ty) t'
elab (PApp subject sp) = pure $ tcApps !(elab subject) !(elabSpine sp)
elab (PHole n) = pure $ tcHole n
elab PUnit = pure $ whenInStage $ \case
  Just Obj => tcPrim PrimTt []
  _ => tcPrim PrimTT []
elab (PSigmas (MkPTel [])) = elab PUnit
elab (PSigmas (MkPTel ((MkPParam l n ty) :: ts))) = do
  ty' <- interceptAll (enterLoc l) <$> elab (fromMaybe (PHole Nothing) ty)
  ts' <- elab (PSigmas (MkPTel ts))
  pure . whenInStage $ \case
    Just Obj => tcPrim PrimSigma [hole, hole, ty', ts']
    _ => tcPrim PrimSIGMA [ty', ts']
elab (PPairs (MkPSpine [])) = elab PUnit
elab (PPairs (MkPSpine ((MkPArg l n t) :: ts))) = do
  t' <- interceptAll (enterLoc l) <$> elab t
  ts' <- elab (PPairs (MkPSpine ts))
  pure . whenInStage $ \case
    Just Obj => tcPrim PrimPair [hole, hole, hole, hole, t', ts']
    _ => tcPrim PrimPAIR [hole, hole, t', ts']
elab (PProj v n) = ?tcProj
elab (PBlock t []) = elab PUnit
elab (PBlock t (PLet l n ty tm :: bs)) = do
  s <- gets stageHint
  ty' <- traverse elab ty
  let statement = tcLet n s ty' !(elab tm) !(elab (PBlock t bs))
  pure $ interceptAll (enterLoc l) statement
elab (PBlock t (PLetRec l n ty tm :: bs)) = do
  s <- gets stageHint
  let statement = tcLetRec n s !(elab ty) !(elab tm) !(elab (PBlock t bs))
  pure $ interceptAll (enterLoc l) statement
elab (PBlock t (PBlockTm l tm :: [])) = elab tm
elab (PBlock t (PDecl l n ty :: bs)) = do
  s <- gets stageHint
  let statement = tcDecl n s !(elab ty) !(elab (PBlock t bs))
  pure $ interceptAll (enterLoc l) statement
elab (PBlock t (PBind l n ty tm :: bs)) = ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) =
  elab (PBlock t (PBind l "_" Nothing tm :: bs))
elab (PBlock t (PDirSt d b :: bs)) = ?fajj
  -- case parseDirective d of
  --     Nothing => ?fa_1
  --     Just MtaDir => ?fa_3
  --     Just ObjDir => ?fa_4
  -- elab (PBlock t (b :: bs)) -- @@TODO
elab (PLit l) = ?todoLit
elab (PDirTm d t) = elab t -- @@TODO