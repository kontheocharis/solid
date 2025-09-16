module Common

import Decidable.Equality
import Decidable.Decidable
import Utils

-- A bound variable is either from an explicit or an implicit pi.
--
-- We remember this in the context.
public export
data PiMode = Explicit | Implicit
            
public export
Show PiMode where
  show Explicit = "explicit"
  show Implicit = "implicit"

public export
DecEq PiMode where
  decEq Explicit Explicit = Yes Refl
  decEq Implicit Implicit = Yes Refl
  decEq Explicit Implicit = No (\Refl impossible)
  decEq Implicit Explicit = No (\Refl impossible)

public export
Eq PiMode where
  a == b = isYes $ decEq a b

public export
Name : Type
Name = String

-- A name is a member of a 'context skeleton'
public export
0 Ident : Type
Ident = (PiMode, Name)

public export
[showIdent] Show Ident where
  show (Explicit, n) = n
  show (Implicit, n) = "[" ++ n ++ "]"

-- The stage we are in
--
-- This is a two-level language.
public export
data Stage = Obj | Mta

public export
DecEq Stage where
  decEq Obj Obj = Yes Refl
  decEq Mta Mta = Yes Refl
  decEq Obj Mta = No (\Refl impossible)
  decEq Mta Obj = No (\Refl impossible)

public export
Eq Stage where
  a == b = isYes (decEq a b)

public export
Show Stage where
  show Mta = "mta"
  show Obj = "obj"