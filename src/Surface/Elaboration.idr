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
import Data.HashMap
import System.Path

public export
record Module where
  constructor MkModule
  name : Input
  presyn : PTm
  syn : Expr [<]

public export
record ProjectAtElab where
  constructor MkProject
  startingPath : Maybe String
  otherModules : HashMap Input Module
  main : Maybe Module
  
export
startingPathL : Lens ProjectAtElab (Maybe String)
startingPathL = MkLens startingPath (\sh, s => { startingPath := sh } s)
  
export
otherModulesL : Lens ProjectAtElab (HashMap Input Module)
otherModulesL = MkLens otherModules (\sh, s => { otherModules := sh } s)
  
export
mainL : Lens ProjectAtElab (Maybe Module)
mainL = MkLens main (\sh, s => { main := sh } s)

public export
record ElabState where
  constructor MkElabState
  project : ProjectAtElab
  stageHint : Maybe Stage
  isPrimitive : Bool
  
export
projectL : Lens ElabState ProjectAtElab
projectL = MkLens project (\sh, s => { project := sh } s)
  
export
stageHintL : Lens ElabState (Maybe Stage)
stageHintL = MkLens stageHint (\sh, s => { stageHint := sh } s)
  
export
isPrimitiveL : Lens ElabState Bool
isPrimitiveL = MkLens isPrimitive (\sh, s => { isPrimitive := sh } s)

export
initialElabState : ElabState
initialElabState = MkElabState (MkProject Nothing empty Nothing) Nothing False
  
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
interface (Monad e, HasTc e, HasState ElabState e) => HasElab (0 e : Type -> Type) where
  elabError : ElabErrorKind -> e x
  parseImport : (filename : Input) -> e PTm
  runTcRoot : Tc e -> e (Expr [<])

-- Elaborate a presyntax term into a typechecking operation.
export covering
elab : HasElab e => PTm -> e (Tc e)

enterLoc : HasElab e => Loc -> e x -> e x
enterLoc l = enter idL l
 
export
whenInStage : HasElab e => (Maybe Stage -> Tc e) -> Tc e
whenInStage f Infer = \ctx, (InferInput maybeStage) =>
  f maybeStage Infer ctx (InferInput maybeStage)
whenInStage f Check = \ctx, (CheckInput stage annot) =>
  f (Just stage) Check ctx (CheckInput stage annot)

covering
elabSpine : HasElab e => PSpine k -> e (List (Ident, Tc e))
elabSpine (MkPSpine []) = pure $ []
elabSpine (MkPSpine (MkPArg l n v :: xs)) = pure $ (
    fromMaybe (Explicit, "_") n,
    wrap (enter idL l) $ !(elab v)
  ) :: !(elabSpine (MkPSpine xs))
  
tc : HasElab e => Tc e -> e (Tc e)
tc f = do
  l <- get Loc
  pure $ wrap (enter idL l) f
  
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
printCtxAnd : HasElab e => e (Tc e) -> e (Tc e)
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
printTermAnd : HasElab e => (expand : Bool) -> e (Tc e) -> e (Tc e)
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
printTypeAnd : HasElab e => (expand : Bool) -> e (Tc e) -> e (Tc e)
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
handleImport : HasElab e => PTm -> e (Tc e)
handleImport (PApp t (MkPSpine [])) = handleImport t
handleImport (PLoc l t) = handleImport t
handleImport t@(PLit (Str path)) = do
  start <- fromMaybe "" <$> access (projectL . startingPathL)
  let completePath = joinPath [start, path]
  let p = FileInput (fromMaybe "." $ parent completePath)
  tm : Expr _ <- lookup p <$> access (projectL . otherModulesL) >>= \case
    Just (MkModule _ _ tm) => pure tm
    Nothing => do
      ptm <- parseImport (FileInput completePath)
      tm <- elab ptm >>= runTcRoot
      update (projectL . otherModulesL) $ insert p (MkModule p ptm tm)
      pure tm
  pure $ return (weakS Terminal tm)
handleImport t = elabError $ ImportMustBeLiteral t

covering
handleDirective : HasElab e => Directive -> DirectivePlacement -> Lazy (e (Tc e)) -> e (Tc e)
handleDirective d p b = case (parseDirective d, p) of
  (Nothing, _) => elabError (UnknownDirective d)
  (Just MtaDir, InBlockSt _) => enter stageHintL (Just Mta) b
  (Just ObjDir, InBlockSt _) => enter stageHintL (Just Obj) b
  (Just PrimitiveDir, InBlockSt _) => enter isPrimitiveL True b
  (Just DebugCtx, _) => printCtxAnd b
  (Just DebugTerm, _) => printTermAnd False b
  (Just DebugTermExp, _) => printTermAnd True b
  (Just DebugType, _) => printTypeAnd False b
  (Just DebugTypeExp, _) => printTypeAnd True b
  (Just Import, InTm t) => handleImport t
  (Just d@Import, InBlockSt t) => elabError $ DirectiveNotAllowed d
  (Just d, InTm _) => elabError $ DirectiveNotAllowed d
  
covering
hole : (HasTc e) => Tc e
hole = tcHole Nothing

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
elab (PBlock t (PLet l n ty tm :: bs)) = enterLoc l $ do
  s <- reset stageHintL
  ty' <- traverse elab ty
  tm' <- elab tm
  bs' <- elab (PBlock t bs)
  tc (tcLet n s ty' tm' bs')
elab (PBlock t (PLetRec l n ty tm :: bs)) = enterLoc l $ do
  s <- reset stageHintL
  ty' <- elab ty
  tm' <- elab tm
  bs' <- elab (PBlock t bs)
  tc $ tcLetRec n s ty' tm' bs'
elab (PBlock t (PBlockTm l tm :: [])) = do
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
  ?todoBind
elab (PBlock t (PBlockTm l tm :: bs)) = do
  elab (PBlock t (PBind l "_" Nothing tm :: bs))
elab (PBlock t (PDirSt d b :: bs)) = handleDirective d (InBlockSt bs) (elab (PBlock t (b :: bs)))
elab (PLit l) = ?todoLit
elab (PDirTm d t) = handleDirective d (InTm t) (elab t)
