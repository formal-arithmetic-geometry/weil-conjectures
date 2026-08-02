/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs

/-!

# Main Statements of Nagata Compactification

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def NagataCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Compactification f := sorry

instance [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

end AlgebraicGeometry
