/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.ReductionIdealPowerQuotient
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitsImageLinearization
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerInclusion

/-! # Comparison of the multiplicative and additive nilradical-power cokernels
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The cokernel of the constructed inclusion of consecutive nilpotent-units kernels
is the additive étale sheaf of the constructed module `N^(j+1)/N^(j+2)`. -/
theorem nonempty_reductionUnitsPowerCokernelIso (X : Scheme.{u}) (j : ℕ) :
    Nonempty (cokernel (X.reductionUnitsPowerInclusion j) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf (X.reductionIdealPowerQuotient j)))) := by
  let f := gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1)).subschemeι
  let g := gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1 + 1)).subschemeι
  let r := kernel.ι f ≫ g
  have hz : X.reductionUnitsPowerInclusion j ≫ r = 0 := by
    dsimp only [r]
    rw [← Category.assoc, X.reductionUnitsPowerInclusion_ι j]
    exact kernel.condition g
  have hk : IsLimit (KernelFork.ofι (X.reductionUnitsPowerInclusion j) hz) := by
    apply KernelFork.IsLimit.ofι'
    intro A k hkr
    refine ⟨kernel.lift g (k ≫ kernel.ι f) hkr, ?_⟩
    apply (cancel_mono (kernel.ι f)).1
    rw [Category.assoc, X.reductionUnitsPowerInclusion_ι j]
    exact kernel.lift_ι g (k ≫ kernel.ι f) hkr
  let S := ShortComplex.mk (X.reductionUnitsPowerInclusion j) r hz
  have he : S.Exact := S.exact_of_f_is_kernel hk
  let e := (cokernelIsCokernel (X.reductionUnitsPowerInclusion j)).coconePointUniqueUpToIso
    he.isColimitImage
  have hII : (X.nilradical ^ (j + 1)) * (X.nilradical ^ (j + 1)) ≤
      X.nilradical ^ (j + 1 + 1) := by
    intro U
    change (X.nilradical.ideal U) ^ (j + 1) * (X.nilradical.ideal U) ^ (j + 1) ≤
      (X.nilradical.ideal U) ^ (j + 1 + 1)
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by omega)
  have hIN : X.nilradical ^ (j + 1) ≤ X.nilradical := by
    intro U
    exact Ideal.pow_le_self (Nat.succ_ne_zero j)
  let : (cokernel (IdealSheafData.toModulesOfLE
      (reduction_nilradical_power_le X j))).IsQuasicoherent :=
    X.isQuasicoherent_reductionIdealPowerQuotient j
  obtain ⟨e'⟩ := nonempty_nilIdealUnitsImageIso X (X.nilradical ^ (j + 1))
    (X.nilradical ^ (j + 1 + 1)) (reduction_nilradical_power_le X j) hII hIN
  exact ⟨e ≪≫ e'⟩

end AlgebraicGeometry.Scheme
