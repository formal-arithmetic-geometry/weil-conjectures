/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Comparison with the limit of a Noetherian approximation

Source: the Weil conjectures blueprint, chapter `sec-nagata-compactification`, unit
`sk-prop-nagata-sketch-approximation`, definition "Comparison from the original scheme to the
inverse limit" (blueprint: def-nagata-glued-limit-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.NoetherianApproximation

/-- The comparison from `S` to the chosen inverse limit of its approximation, induced by the
compatible chart maps recorded in `N.π`. Its composite with each limit projection is the
corresponding map `N.π.app i`, by `limit.lift_π`. The `HasLimit` parameter only selects a limit:
existence already follows from `N.isLimit`.

Source: Weil conjectures blueprint, `sk-prop-nagata-sketch-approximation`, definition
"Comparison from the original scheme to the inverse limit"
(blueprint: def-nagata-glued-limit-comparison). -/
noncomputable def gluedLimitComparison {S : Scheme.{u}} (N : S.NoetherianApproximation)
    [HasLimit N.D] : S ⟶ limit N.D :=
  limit.lift N.D (Cone.mk S N.π)

end AlgebraicGeometry.Scheme.NoetherianApproximation
