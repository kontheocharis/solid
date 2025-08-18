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
  locHint : Maybe Loc
  
stageHintL : Lens ElabState (Maybe Stage)
stageHintL = MkLens stageHint (\sh, s => { stageHint := sh } s)
  
locHintL : Lens ElabState (Maybe Loc)
locHintL = MkLens locHint (\sh, s => { locHint := sh } s)
  
export
data ElabErrorKind : Type where
  UnknownDirective : Directive -> ElabErrorKind
  
export
record ElabError where
  constructor MkElabError
  kind : ElabErrorKind
  loc : Loc
  
export
Show ElabError where
  show t = ?showElabError

export
0 Elab : Type -> Type
Elab a = EitherT ElabError (State ElabState) a

export
initialElabState : ElabState
initialElabState = MkElabState Nothing Nothing

export
runElab : Elab x -> Either ElabError x
runElab = evalState initialElabState . runEitherT 

export
elabError : ElabErrorKind -> Elab x
elabError k = do
  l <- gets locHint
  throwE (MkElabError k (fromMaybe dummyLoc l))

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
  
tc : HasTc m => TcAll m -> Elab (TcAll m)
tc f = do
  l <- access locHintL
  case l of
    Just l' => pure $ interceptAll (enterLoc l') f
    Nothing => pure f
  
covering
hole : HasTc m => TcAll m
hole = tcHole Nothing

enterLoc : Loc -> Elab x -> Elab x
enterLoc l = enter locHintL (Just l)

enterStage : Stage -> Elab x -> Elab x
enterStage s = enter stageHintL (Just s)

covering
handleDirective : Directive -> Elab x -> Elab x
handleDirective d b = case parseDirective d of
  Nothing => elabError (UnknownDirective d)
  Just MtaDir => enterStage Mta b
  Just ObjDir => enterStage Obj b

elab (PLoc l t) = enterLoc l $ elab t
elab (PName n) = tc (tcVar n)
elab (PLam (MkPTel []) t) = elab t
elab (PLam (MkPTel ((MkPParam l n ty) :: xs)) t) = do
  t' <- elab (PLam (MkPTel xs) t)
  ty <- enterLoc l $ traverse elab ty
  tc $ tcLam n ty t'
elab (PPi (MkPTel []) t) = elab t
elab (PPi (MkPTel ((MkPParam l n ty) :: xs)) t) = do
  t' <- elab (PPi (MkPTel xs) t)
  let ty' = fromMaybe (PHole Nothing) ty
  ty <- enterLoc l $ elab ty'
  tc $ tcPi n ty t'
elab (PApp subject sp) = tc $ tcApps !(elab subject) !(elabSpine sp)
elab (PHole n) = tc $ tcHole n
elab PUnit = tc $ whenInStage $ \case
  Just Obj => tcPrim PrimTt []
  _ => tcPrim PrimTT []
elab (PSigmas (MkPTel [])) = elab PUnit
elab (PSigmas (MkPTel ((MkPParam l n ty) :: ts))) = do
  ty' <- enterLoc l $ elab (fromMaybe (PHole Nothing) ty)
  ts' <- elab (PSigmas (MkPTel ts))
  tc . whenInStage $ \case
    Just Obj => tcPrim PrimSigma [hole, hole, ty', ts']
    _ => tcPrim PrimSIGMA [ty', ts']
elab (PPairs (MkPSpine [])) = elab PUnit
elab (PPairs (MkPSpine ((MkPArg l n t) :: ts))) = do
  t' <- enterLoc l $ elab t
  ts' <- elab (PPairs (MkPSpine ts))
  tc . whenInStage $ \case
    Just Obj => tcPrim PrimPair [hole, hole, hole, hole, t', ts']
    _ => tcPrim PrimPAIR [hole, hole, t', ts']
elab (PProj v n) = ?tcProj
elab (PBlock t []) = elab PUnit
elab (PBlock t (PLet l n ty tm :: bs)) = enterLoc l $ do
  s <- access stageHintL
  ty' <- traverse elab ty
  tc (tcLet n s ty' !(elab tm) !(elab (PBlock t bs)))
elab (PBlock t (PLetRec l n ty tm :: bs)) = enterLoc l $ do
  s <- access stageHintL
  tc $ tcLetRec n s !(elab ty) !(elab tm) !(elab (PBlock t bs))
elab (PBlock t (PBlockTm l tm :: [])) = enterLoc l $ elab tm
elab (PBlock t (PDecl l n ty :: bs)) = enterLoc l $ do
  s <- access stageHintL
  tc $ tcDecl n s !(elab ty) !(elab (PBlock t bs))
elab (PBlock t (PBind l n ty tm :: bs)) = ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) =
  elab (PBlock t (PBind l "_" Nothing tm :: bs))
elab (PBlock t (PDirSt d b :: bs)) = handleDirective d (elab (PBlock t bs))
elab (PLit l) = ?todoLit
elab (PDirTm d t) = handleDirective d (elab t)
