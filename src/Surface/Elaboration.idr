-- Elaboration of surface syntax to core syntax.
module Surface.Elaboration

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Core.Atoms
import Core.Typechecking
import Surface.Presyntax
import Data.Maybe

covering
elab : (HasTc m) => {md : TcMode} -> PTm -> Tc md m

covering
elabSpine : (HasTc m) => PSpine Functions -> List (Ident, Tc Check m)

elabSpine (MkPSpine []) = []
elabSpine (MkPSpine (MkPArg l n v :: xs))
  = (fromMaybe (Explicit, "_") n, intercept (enterLoc l) $ elab v) :: elabSpine (MkPSpine xs)

elab (PLoc l t) = intercept (enterLoc l) $ elab t
elab (PName n) = switch $ tcVar n
elab (PLam (MkPTel []) t) = elab t
elab (PLam (MkPTel ((MkPParam l n ty) :: xs)) t)
  = let t' = elab (PLam (MkPTel xs) t) in
    tcLam n (intercept (enterLoc l) <$> (elab <$> ty)) t'
elab (PApp subject sp) = switch $ tcApp (elab subject) (elabSpine sp)
elab (PPi (MkPTel []) t) = elab t
elab (PPi (MkPTel ((MkPParam l n ty) :: xs)) t)
  = let t' = elab (PPi (MkPTel xs) t) in
    let ty' = fromMaybe (PHole Nothing) ty in
    switch $ tcPi n (intercept (enterLoc l) $ elab ty') t'
elab (PHole n) = tcHole n
elab PUnit = ?elab_missing_case_4
elab (PSigmas _) = ?elab_missing_case_5
elab (PPairs _) = ?elab_missing_case_6
elab (PBlock _ _) = ?elab_missing_case_8
elab (PProj _ _) = ?elab_missing_case_9
elab (PLit _) = ?elab_missing_case_11
