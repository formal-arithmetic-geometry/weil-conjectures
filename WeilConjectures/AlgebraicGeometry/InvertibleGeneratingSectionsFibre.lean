/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The fibre criterion for generating an invertible module

## References

* Stacks Project, Modules, Definition 01AM and Lemma 01CY; Sheaves, Lemma 0H7H.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private lemma rankOne_span_iff {R M I : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (v : I → M) :
    Submodule.span R (Set.range v) = ⊤ ↔
      ∃ i, v i ∉ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) := by
  classical
  have hm : ∀ x : M, x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) ↔
      e x ∈ IsLocalRing.maximalIdeal R := by
    intro x
    have hh : ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)).map
        e.toLinearMap = IsLocalRing.maximalIdeal R := by
      simp only [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
        Ideal.smul_eq_mul, Ideal.mul_top]
    have hmem : e x ∈ IsLocalRing.maximalIdeal R ↔
        x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) := by
      simpa only [hh, LinearEquiv.symm_apply_apply] using
      (Submodule.mem_map_equiv
        ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)) (e := e) (x := e x))
    exact hmem.symm
  constructor
  · intro h
    by_contra! hn
    have hs : Submodule.span R (Set.range v) ≤
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hn i)
    have h1 := hs (h ▸ (Submodule.mem_top : e.symm 1 ∈ (⊤ : Submodule R M)))
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa using (hm _).mp h1
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ this
      isUnit_one)
  · rintro ⟨i, hi⟩
    have hu : IsUnit (e (v i)) := IsLocalRing.notMem_maximalIdeal.mp (mt (hm _).mpr hi)
    rcases hu with ⟨a, ha⟩
    apply top_unique
    intro x _
    have hx : x = ((e x) * ↑a⁻¹) • v i := by
      apply e.injective
      simp [ha.symm]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The sections `s 0, …, s n` generate an invertible module if and only if at every point
one has nonzero residue-field value, equivalently their nonvanishing loci cover the scheme.
The value is nonzero exactly when the germ lies outside the maximal ideal times the stalk,
which is the definition of `nonvanishingLocus`. Compatible sections in `L.sections` are
identified with global sections by evaluation at the terminal open `⊤`. -/
theorem invertible_generating_sections_fibre_criterion (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → L.sections) :
    (Epi (L.freeHomEquiv.symm s) ↔
      ∀ y : Y, ∃ i, y ∈ nonvanishingLocus L ((s i).val (Opposite.op ⊤))) ∧
    (Epi (L.freeHomEquiv.symm s) ↔
      (⋃ i, nonvanishingLocus L ((s i).val (Opposite.op ⊤))) = Set.univ) := by
  have h : Epi (L.freeHomEquiv.symm s) ↔
      ∀ y : Y, ∃ i, y ∈ nonvanishingLocus L ((s i).val (Opposite.op ⊤)) := by
    rw [generating_sections_iff_stalk_span]
    apply forall_congr'
    intro y
    obtain ⟨e⟩ := invertible_stalk_linearEquiv Y L y
    exact rankOne_span_iff e _
  refine ⟨h, h.trans ?_⟩
  rw [Set.eq_univ_iff_forall]
  simp only [Set.mem_iUnion]

end AlgebraicGeometry.Scheme.Modules
