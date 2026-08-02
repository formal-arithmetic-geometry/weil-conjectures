/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.NagataCompactification.Defs

/-!

# Main Statements of Nageta Compactification

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def NagataCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Compactification f := sorry

instance [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

end AlgebraicGeometry
