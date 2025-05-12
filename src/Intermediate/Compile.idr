module Intermediate.Compile

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Core.Base
import Intermediate.Syntax

%default covering

-- Rust programs are just represented by a String for now.
Rust : Type
Rust = String

-- Environments map variables to Rust programs.
Env : Ctx -> Type
Env = Con.Con (const Rust)

-- Monad for compilation. We store the current environment in a reader.
-- The integer is used to generate fresh names.
Compiler : Ctx -> Type -> Type
Compiler ns = ReaderT (Env ns) (State Int) 

-- Generate a fresh name.
fresh : Compiler ns Rust
fresh = do
  k <- get
  put (k + 1)
  pure "x\{show k}"

-- Bind a local variable.
bind : Rust -> Compiler (ns :< n) a -> Compiler ns a
bind v c = MkReaderT $ \env => runReaderT (env :< v) c 

-- Compile a term to a Rust program.
-- Current implementation details:
--   - Every type is represented as an array of bytes.
--   - Every lambda is boxed.
comp : ITerm ns -> Compiler ns Rust
comp = \case
  IVar i => ?h -- need function to lookup variable in Con. Then call .clone
  ILam _ i x => do
    v <- fresh
    x' <- bind v $ comp x
    pure "Rc::new(move |\{v} : [u8; \{show i}]| \{x'})" -- For now all functions are reference counted.
  IApp x y => do
    x' <- comp x
    y' <- comp y
    pure "\{x'}(\{y'})"
  ILet _ x y => do
    v <- fresh
    x' <- comp x
    y' <- bind v $ comp y
    pure "{ let \{v} = \{x'}; \{y'} }"
  IPair i j x y => do
    x' <- comp x
    y' <- comp y
    pure "{ let fst = \{x'}; let snd = \{y'}; let mut bits = [0; \{show $ i + j}]; bits[..\{show i}].copy_from_slice(&fst); bits[\{show i}..].copy_from_slice(&snd); bits }"