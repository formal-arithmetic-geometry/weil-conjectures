/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPresheafComparison

/-! # Compatibility with the upstream exterior-power sheaf -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The original exterior sheaf is the upstream exterior-power sheaf.
Source: the sectionwise exterior-power constructions, followed by the same sheafification
functor (blueprint: lem-sc-exterior-sheaf-upstream-comparison).

Proof: both sheaves are obtained by the same sheafification functor. Their input
presheaves agree by uniqueness of the semilinear restriction maps on pure wedges.
Applying the sheafification functor to that equality gives the assertion. This uses no
freeness, positive-rank, or nonzero-ring assumption. -/
theorem exteriorSheaf_eq_exteriorPower {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n = exteriorPower M n := by
  exact congrArg
    (fun P ↦ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
    (exteriorSheafPresheaf_eq_exteriorPower M n)

end AlgebraicGeometry.Scheme.Modules
