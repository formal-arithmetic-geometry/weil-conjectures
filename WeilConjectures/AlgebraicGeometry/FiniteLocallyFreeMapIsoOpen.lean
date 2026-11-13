/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocusPullback
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback

/-! # The universal isomorphism open of a map of vector bundles

## References

* Stacks Project, Tags 0BDP and 05GD
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The locus where a map of finite locally free modules becomes invertible is a
quasi-compact open immersion, with its universal property on arbitrary test schemes.
(Stacks, Tags 0BDP and 05GD) -/
theorem exists_finiteLocallyFreeMapIsoOpen {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N) :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ W), IsOpenImmersion k ∧ QuasiCompact k ∧
      ∀ {T : Scheme.{u}} (h : T ⟶ W),
        (∃ l : T ⟶ Z, l ≫ k = h) ↔ IsIso ((tensorPullback h).map φ) := by
  let U := moduleMapIsoLocus φ
  have hqc : QuasiCompact U.ι := by
    apply (quasiCompact_iff_forall_isAffineOpen (f := U.ι)).2
    intro V hV
    apply (U.ι.isOpenEmbedding.isEmbedding.isCompact_iff).2
    change IsCompact (U.ι '' (U.ι ⁻¹' (V : Set W)))
    simpa only [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι] using
      isCompact_moduleMapIsoLocus_inter M N φ V hV
  refine ⟨U.toScheme, U.ι, inferInstance, hqc, ?_⟩
  intro T h
  constructor
  · rintro ⟨l, hl⟩
    apply isIso_tensorPullback_of_range_subset_moduleMapIsoLocus φ h
    rw [← hl]
    exact Set.Subset.trans (Set.range_comp_subset_range l U.ι)
      (by simp [Scheme.Opens.range_ι, U])
  · intro hφ
    have hh := range_subset_moduleMapIsoLocus_of_isIso_tensorPullback M N φ h hφ
    have hh' : Set.range h ⊆ Set.range U.ι := by
      simpa only [Scheme.Opens.range_ι] using hh
    exact ⟨IsOpenImmersion.lift U.ι h hh', IsOpenImmersion.lift_fac U.ι h hh'⟩

end AlgebraicGeometry.Scheme.Modules
