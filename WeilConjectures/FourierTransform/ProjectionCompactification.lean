/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Ordinary étale projection compactification lower shriek

Source: the compactification convention used in Stacks Project, `more-etale.tex`,
Tag 0GKX (blueprint: def-weil-pbc-projection-compactification).

The previously recorded dependency declaration described a pro-étale ring-coefficient
construction. This module records the ordinary étale fixed-coefficient construction required
by the dependency: for a compactification `c = (j, p)`, bounded-below `Rf_!` is the derived
extension by zero along `j` followed by the bounded-below right derived direct image along `p`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The bounded-below ordinary étale lower shriek attached to a compactification is the
composition of derived extension by zero and bounded-below derived direct image.

Source: Stacks Project, `more-etale.tex`, Tag 0GKX, compactification convention
(blueprint: def-weil-pbc-projection-compactification).
-/
theorem projectionCompactification_lowerShriek_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [QuasiCompact c.i] :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c =
      D+((c.i)_!open[ModuleCat.{u + 1} A]) ⋙
        R+((c.g)_*[ModuleCat.{u + 1} A]) := by
  sorry

end AlgebraicGeometry.Etale
