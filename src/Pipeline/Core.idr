module Pipeline.Core

import Utils
import Data.Morphisms
import Data.Vect
import Data.Vect.Elem

public export
data Stages : (Type -> Type) -> Nat -> Type where
  Nil : Stages k 0
  (::) : {out : Type} -> k out -> Stages k n -> Stages k (S n)
  
public export
0 Head : Stages k (S n) -> Type
Head ((::) {out} a _) = out

public export
0 Last : Stages k (S n) -> Type
Last ((::) {out} _ (Nil)) = out
Last ((::) {out} _ (b :: xs)) = Last (b :: xs)

public export
data Elem : (k : Type -> Type) -> (out : Type) -> k out -> Stages k n -> Type where
  Here : {0 s : k out} -> {ss : Stages k n} -> Elem k out s ((::) {out = out} s ss)
  There : {0 s : k out} -> {0 s' : k out'} -> Elem k out s ss -> Elem k out s (s' :: ss)

public export
0 Vertices : (Type -> Type) -> Nat -> Type
Vertices k n = Stages k (S (S n))

public export
0 Pipeline : (k : Type -> Type) -> (m : Type -> Type) -> Vertices k n -> Type
Pipeline k m ((::) {out = elA} a ((::) {out = elB} b [])) = elA -> m elB
Pipeline k m ((::) {out = elA} a ((::) {out = elB} b (c :: xs))) = (elA -> m elB, Pipeline k m (b :: c :: xs))

public export
runPipeline : Monad m => {v : Vertices k n}
  -> Pipeline k m v
  -> Head v -> m (Last v)
runPipeline {v = [a, b]} p x = p x
runPipeline {v = (a :: b :: c :: xs)} (p, q) x = p x >>= runPipeline q

public export
runPipelineUntil : Monad m => {v : Vertices k n}
  -> Pipeline k m v
  -> Elem k out end v 
  -> Head v -> m out
runPipelineUntil p Here x = pure x
runPipelineUntil {v = [a, b]} p (There elem) x with (elem)
  _ | Here = p x
  _ | There _ impossible
runPipelineUntil {v = (a :: b :: c :: xs)} (p, q) (There elem) x = p x >>= runPipelineUntil q elem

public export
get : {k : Type -> Type} -> (x : k out) -> {xs : Stages k n} -> (Elem k out x xs) => Elem k out x xs
get _ @{el} = el