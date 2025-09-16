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
import Core.Evaluation
import Core.Combinators
import Core.Metavariables
import Core.Context
import Core.Typechecking
import Core.Primitives.Definitions
import Core.Primitives.Rules
import Core.Primitives.Typing
import Surface.Presyntax
import Core.Syntax
import Data.Maybe
import Control.Monad.State
import Control.Monad.Error.Either
import Debug.Trace
import Surface.Unelaboration

export
record ElabState where
  constructor MkElabState
  stageHint : Maybe Stage
  locHint : Maybe Loc
  isPrimitive : Bool
  
stageHintL : Lens ElabState (Maybe Stage)
stageHintL = MkLens stageHint (\sh, s => { stageHint := sh } s)
  
locHintL : Lens ElabState (Maybe Loc)
locHintL = MkLens locHint (\sh, s => { locHint := sh } s)
  
isPrimitiveL : Lens ElabState Bool
isPrimitiveL = MkLens isPrimitive (\sh, s => { isPrimitive := sh } s)
  
export
data ElabErrorKind : Type where
  UnknownDirective : Directive -> ElabErrorKind
  DirectiveNotAllowed : KnownDirective -> ElabErrorKind
  DeclNotSupported : ElabErrorKind
  
export
Show ElabErrorKind where
  show (UnknownDirective (MkDirective d)) = "Unknown directive `#\{d}`"
  show (DirectiveNotAllowed d) = "Directive `#\{d.asDirective.name}` is not allowed here"
  show DeclNotSupported = "Non-primitive declarations without definitions are not supported yet"
  
export
record ElabError where
  constructor MkElabError
  kind : ElabErrorKind
  loc : Loc
  
export
Show ElabError where
  show (MkElabError k l) = "Elaboration error at \{show l}:\n\{show k}"

export
0 Elab : Type -> Type
Elab a = EitherT ElabError (State ElabState) a

export
initialElabState : ElabState
initialElabState = MkElabState Nothing Nothing False

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
-- mainAnnot = (objZ (PrimIO $> [
--     (Val _, PrimZeroLayout $> []),
--     (Val _, PrimUnit $> [])])
--   ).f.a
mainAnnot = (objZ (PrimUnit $> [])).f.a
 
export
whenInStage : HasTc m => (Maybe Stage -> TcAll m) -> TcAll m
whenInStage f Infer = \ctx, (InferInput maybeStage) =>
  f maybeStage Infer ctx (InferInput maybeStage)
whenInStage f Check = \ctx, (CheckInput stage annot) =>
  f (Just stage) Check ctx (CheckInput stage annot)

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

resetIsPrimitive : Elab Bool
resetIsPrimitive = do
  p <- access isPrimitiveL
  set isPrimitiveL False
  pure p

ensureNotPrimitive : Elab ()
ensureNotPrimitive = resetIsPrimitive >>= \case
  True => elabError $ DirectiveNotAllowed PrimitiveDir
  False => pure ()

data DirectivePlacement = InTm | InBlockSt

covering
printCtxAnd : HasTc x => Elab (TcAll x) -> Elab (TcAll x)
printCtxAnd b = do
  b' <- b
  tc $ interceptContext (\ctx => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- getLoc
      dbg "--- <Context at \{show loc}> ---"
      dbg (show @{showUnelab {unel = unelabContext {onlyBinds = False}}} ctx)
      dbg "--- </Context> ---\n"
    ) b'

covering
printTermAnd : HasTc x => (expand : Bool) -> Elab (TcAll x) -> Elab (TcAll x)
printTermAnd expand b = do
  b' <- b
  tc $ interceptTerm (\ctx, tm => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- getLoc
      let term : Atom _ = if expand
                    then expandDefs ctx.scope.defs tm.mp.tm
                    else tm.mp.tm
      dbg "--- <Term at \{show loc}> ---"
      dbg (show @{showUnelab} term)
      dbg "--- </Term> ---\n"
    ) b'

covering
printTypeAnd : HasTc x => (expand : Bool) -> Elab (TcAll x) -> Elab (TcAll x)
printTypeAnd expand b = do
  b' <- b
  tc $ interceptTerm (\ctx, tm => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- getLoc
      let type : Atom _ = if expand
                    then expandDefs ctx.scope.defs tm.mp.annot.ty
                    else tm.mp.annot.ty
      dbg "--- <Type at \{show loc}> ---"
      dbg (show @{showUnelab} type)
      dbg "--- </Type> ---\n"
    ) b'

covering
handleDirective : HasTc x => Directive -> DirectivePlacement -> Elab (TcAll x) -> Elab (TcAll x)
handleDirective d p b = case (parseDirective d, p) of
  (Nothing, _) => elabError (UnknownDirective d)
  (Just MtaDir, InBlockSt) => enter stageHintL (Just Mta) b
  (Just ObjDir, InBlockSt) => enter stageHintL (Just Obj) b
  (Just PrimitiveDir, InBlockSt) => enter isPrimitiveL True b
  (Just DebugCtx, _) => printCtxAnd b
  (Just DebugTerm, _) => printTermAnd False b
  (Just DebugTermExp, _) => printTermAnd True b
  (Just DebugType, _) => printTypeAnd False b
  (Just DebugTypeExp, _) => printTypeAnd True b
  (Just d, InTm) => elabError $ DirectiveNotAllowed d

elab (PLoc l t) =
  -- @@Debugging
  -- trace "elaborating \{show t}" $
  enterLoc l $ elab t
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
elab (PName n) with (nameToPrim n) 
  _ | Just (MkPrimitiveAny {level = PrimNative} p) = tc (tcPrimUser p [])
  _ | _ = tc (tcVar n)
elab (PApp subject@(PName n) sp) with (nameToPrim n)
  _ | Just (MkPrimitiveAny {level = PrimNative} p) = tc $ tcPrimUser p !(elabSpine sp)
  _ | _ = tc $ tcApps !(elab subject) !(elabSpine sp)
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
elab (PBlock t []) = do
  elab PUnit
  -- -- @@Debugging
  -- tc (interceptContext (\ctx => do
  --   let Val _ = ctx.idents 
  --   mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
  --   trace (show @{showUnelab} ctx) (pure ())) e)
elab (PBlock t (PLet l n ty tm :: bs)) = enterLoc l $ ensureNotPrimitive >> do
  s <- reset stageHintL
  ty' <- traverse elab ty
  tm' <- elab tm
  bs' <- elab (PBlock t bs)
  tc (tcLet n s ty' tm' bs')
elab (PBlock t (PLetRec l n ty tm :: bs)) = enterLoc l $ ensureNotPrimitive >> do
  s <- reset stageHintL
  ty' <- elab ty
  tm' <- elab tm
  bs' <- elab (PBlock t bs)
  tc $ tcLetRec n s ty' tm' bs'
elab (PBlock t (PBlockTm l tm :: [])) = ensureNotPrimitive >> do
  enterLoc l $ elab tm
elab (PBlock t (PDecl l n ty :: bs)) = enterLoc l $ do
  s <- reset stageHintL
  p <- resetIsPrimitive
  if p
    then do
      ty' <- elab ty
      bs' <- elab (PBlock t bs)
      tc $ tcPrimDecl n s ty' bs'
    else elabError DeclNotSupported
elab (PBlock t (PBind l n ty tm :: bs)) = do
  ensureNotPrimitive
  ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) = ensureNotPrimitive >> do
  elab (PBlock t (PBind l "_" Nothing tm :: bs))
elab (PBlock t (PDirSt d b :: bs)) = handleDirective d InBlockSt (elab (PBlock t (b :: bs)))
elab (PLit l) = ?todoLit
elab (PDirTm d t) = handleDirective d InTm (elab t)
