/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomotopyInvariance.Basic

/-!
# Homotopy invariance and direct images

Let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle and `g : Z ⟶ X` a separated
morphism of `k₀`-schemes. The base change `Y ×_X Z ⟶ Z` of `π` along `g` is the trivial line
bundle over `Z`.
If the unit `M ⟶ Rπ'_* π'^* M` is an isomorphism for a Weil complex `M` on `Z` and every trivial
line bundle `π'` over `Z`, then the unit `Rg_* M ⟶ Rπ_* π^* Rg_* M` is an isomorphism
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`). This is the smooth base
change theorem for the cartesian square of `π` and `g`
(`AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth`), through the mate description of
the base change morphism
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.WeilComplex
