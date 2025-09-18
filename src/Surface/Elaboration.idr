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

public export
record ElabState where
  constructor MkElabState
  stageHint : Maybe Stage
  isPrimitive : Bool
  
stageHintL : Lens ElabState (Maybe Stage)
stageHintL = MkLens stageHint (\sh, s => { stageHint := sh } s)
  
isPrimitiveL : Lens ElabState Bool
isPrimitiveL = MkLens isPrimitive (\sh, s => { isPrimitive := sh } s)

export
initialElabState : ElabState
initialElabState = MkElabState Nothing False
  
export
data ElabErrorKind : Type where
  UnknownDirective : Directive -> ElabErrorKind
  DirectiveNotAllowed : KnownDirective -> ElabErrorKind
  ImportMustBeLiteral : PTm -> ElabErrorKind
  DeclNotSupported : ElabErrorKind
  
export covering
Show ElabErrorKind where
  show (UnknownDirective (MkDirective d)) = "Unknown directive `#\{d}`"
  show (DirectiveNotAllowed d) = "Directive `#\{d.asDirective.name}` is not allowed here"
  show DeclNotSupported = "Non-primitive declarations without definitions are not supported yet"
  show (ImportMustBeLiteral s) = "Imports must be on literal strings, but got term \{show s}"
  
public export
record ElabError where
  constructor MkElabError
  kind : ElabErrorKind
  loc : Loc
  
export covering
Show ElabError where
  show (MkElabError k l) = "Elaboration error at \{show l}:\n\{show k}"
  
public export
interface (Monad e, HasState Loc e, HasState ElabState e) => HasElab (0 e : Type -> Type) where
  elabError : ElabErrorKind -> e x
  parseImport : (filename : String) -> e PTm

-- Elaborate a presyntax term into a typechecking operation.
export covering
elab : (HasElab e, HasTc m) => PTm -> e (TcAll m)

enterLoc : HasElab e => Loc -> e x -> e x
enterLoc l = enter idL l
 
export
whenInStage : HasTc m => (Maybe Stage -> TcAll m) -> TcAll m
whenInStage f Infer = \ctx, (InferInput maybeStage) =>
  f maybeStage Infer ctx (InferInput maybeStage)
whenInStage f Check = \ctx, (CheckInput stage annot) =>
  f (Just stage) Check ctx (CheckInput stage annot)

covering
elabSpine : (HasElab e, HasTc m) => PSpine k -> e (List (Ident, TcAll m))
elabSpine (MkPSpine []) = pure $ []
elabSpine (MkPSpine (MkPArg l n v :: xs)) = pure $ (
    fromMaybe (Explicit, "_") n,
    wrap (enter idL l) $ !(elab v)
  ) :: !(elabSpine (MkPSpine xs))
  
tc : (HasElab e, HasTc m) => TcAll m -> e (TcAll m)
tc f = do
  l <- get Loc
  pure $ wrap (enter idL l) f
  
covering
hole : (HasTc m) => TcAll m
hole = tcHole Nothing

resetIsPrimitive : HasElab e => e Bool
resetIsPrimitive = do
  p <- access isPrimitiveL
  set isPrimitiveL False
  pure p

ensureNotPrimitive : HasElab e => e ()
ensureNotPrimitive = resetIsPrimitive >>= \case
  True => elabError $ DirectiveNotAllowed PrimitiveDir
  False => pure ()

data DirectivePlacement = InTm PTm | InBlockSt (List PBlockStatement)

covering
printCtxAnd : (HasTc x, HasElab e) => e (TcAll x) -> e (TcAll x)
printCtxAnd b = do
  b' <- b
  tc $ runBefore (\ctx => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- get Loc
      dbg "--- <Context at \{show loc}> ---"
      dbg (show @{showUnelab {unel = unelabContext {onlyBinds = False}}} ctx)
      dbg "--- </Context> ---\n"
    ) b'

covering
printTermAnd : (HasTc x, HasElab e) => (expand : Bool) -> e (TcAll x) -> e (TcAll x)
printTermAnd expand b = do
  b' <- b
  tc $ runAfter (\ctx, tm => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- get Loc
      let term : Atom _ = if expand
                    then expandDefs ctx.scope.defs tm.mp.tm
                    else tm.mp.tm
      dbg "--- <Term at \{show loc}> ---"
      dbg (show @{showUnelab} term)
      dbg "--- </Term> ---\n"
    ) b'

covering
printTypeAnd : (HasTc x, HasElab e) => (expand : Bool) -> e (TcAll x) -> e (TcAll x)
printTypeAnd expand b = do
  b' <- b
  tc $ runAfter (\ctx, tm => do
      let Val _ = ctx.idents 
      mtas <- enterMetas (getAllMetas {sm = SolvingNotAllowed} @{metas})
      loc <- get Loc
      let type : Atom _ = if expand
                    then expandDefs ctx.scope.defs tm.mp.annot.ty
                    else tm.mp.annot.ty
      dbg "--- <Type at \{show loc}> ---"
      dbg (show @{showUnelab} type)
      dbg "--- </Type> ---\n"
    ) b'
    
covering
handleImport : (HasTc x, HasElab e) => PTm -> e (TcAll x)
handleImport (PApp t (MkPSpine [])) = handleImport {x = x} t
handleImport (PLoc l t) = handleImport {x = x} t
handleImport t@(PLit (Str path)) = do
  tm <-  parseImport path
  elab tm
handleImport t = elabError $ ImportMustBeLiteral t

covering
handleDirective : (HasTc x, HasElab e) => Directive -> DirectivePlacement -> Lazy (e (TcAll x)) -> e (TcAll x)
handleDirective d p b = case (parseDirective d, p) of
  (Nothing, _) => elabError (UnknownDirective d)
  (Just MtaDir, InBlockSt _) => enter stageHintL (Just Mta) b
  (Just ObjDir, InBlockSt _) => enter stageHintL (Just Obj) b
  (Just PrimitiveDir, InBlockSt _) => enter isPrimitiveL True b
  (Just DebugCtx, _) => printCtxAnd {x = x} b
  (Just DebugTerm, _) => printTermAnd {x = x} False b
  (Just DebugTermExp, _) => printTermAnd {x = x} True b
  (Just DebugType, _) => printTypeAnd {x = x} False b
  (Just DebugTypeExp, _) => printTypeAnd {x = x} True b
  (Just Import, InTm t) => handleImport {x = x} t
  (Just d@Import, InBlockSt t) => elabError $ DirectiveNotAllowed d
  (Just d, InTm _) => elabError $ DirectiveNotAllowed d
  
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
elab (PApp (PLoc l t) sp) = enterLoc l $ elab (PApp t sp) -- hack cause we pattern match on subject
elab (PApp subject@(PName n) sp) with (nameToPrim n)
  _ | Just (MkPrimitiveAny {level = PrimNative} p) = tc $ tcPrimUser p !(elabSpine sp)
  _ | _ = tc $ tcApps !(elab subject) !(elabSpine sp)
elab (PApp subject sp) = tc $ tcApps !(elab subject) !(elabSpine sp)
elab (PHole n) = tc $ tcHole n
elab PUnit = tc $ whenInStage $ \case
  Just Obj => tcPrim PrimTt []
  _ => tcPrim PrimTT []
elab (PSigmas (MkPTel [])) = tc . whenInStage $ \case
  Just Obj => tcPrim PrimUnit []
  _ => tcPrim PrimUNIT []
elab (PSigmas (MkPTel ((MkPParam l n ty) :: ts))) = do
  ty' <- enterLoc l $ elab (fromMaybe (PHole Nothing) ty)
  ts' <- elab (PLam (MkPTel [MkPParam l n Nothing]) (PSigmas (MkPTel ts)))
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
  -- tc (runBefore (\ctx => do
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
elab (PBlock t (PDirSt d b :: bs)) = handleDirective {x = m} d (InBlockSt bs) (elab (PBlock t (b :: bs)))
elab (PLit l) = ?todoLit
elab (PDirTm d t) = handleDirective {x = m} d (InTm t) (elab t)
