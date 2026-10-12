/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology

/-!
# Compactly supported cohomology of a shifted Weil complex

The compactly supported cohomology of the shift `L[1]` of a Weil complex is that of `L`,
shifted: `H_c^r(L[1]) ≅ H_c^{r+1}(L)`, Frobenius-equivariantly
(`AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_shift`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology of a shifted Weil complex: `H_c^r(L[1]) ≅ H_c^{r+1}(L)`,
the direct image with compact support commuting with shifts. -/
theorem nonempty_equiv_compactlySupportedCohomology_shift (L : WeilComplex k₀ l X) (r : ℤ) :
    Nonempty (((L⟦(1 : ℤ)⟧).compactlySupportedCohomology r).Equiv
      (L.compactlySupportedCohomology (r + 1))) :=
  ⟨WeilSheaf.globalSectionsEquivOfIso ((homologySheaf r).mapIso
    (((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).commShiftIso (1 : ℤ)).app L) ≪≫
      homologySheafShiftIso _ 1 r (r + 1) (add_comm 1 r))⟩

end AlgebraicGeometry.WeilComplex
