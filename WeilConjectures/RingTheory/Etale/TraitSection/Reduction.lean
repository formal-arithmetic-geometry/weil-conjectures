/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import WeilConjectures.Mathlib.RingTheory.TotallySplit

/-!
# Tools for the reduction of the trait case to a base containing roots of unity

* `IsLocalization.AtPrime.isDiscreteValuationRing_of_height_eq_one`: the localization of a
  Noetherian integrally closed domain at a height one prime is a discrete valuation ring.
* `Algebra.etale_and_finite_of_isLocalHom`: finite étaleness descends along a flat local
  homomorphism of local rings.

These are used in the reduction of the trait case of blueprint
`sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]) to a base containing the roots of unity.
-/

@[expose] public section

open TensorProduct

/-- The localization of a Noetherian integrally closed domain at a height one prime is a discrete
valuation ring. -/
theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_height_eq_one {R : Type*} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    (hq : q.height = 1) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A q] :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  have hq0 : q.primeCompl ≤ nonZeroDivisors R := q.primeCompl_le_nonZeroDivisors
  have : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors (M := q.primeCompl) A hq0
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization (R := R) (S := A)
    q.primeCompl hq0
  have hd : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q A, hq]
    rfl
  have := IsRegularLocalRing.of_isIntegrallyClosed A hd.le
  exact ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing A hd⟩

/-- Finite étaleness descends along a flat local homomorphism of local rings. -/
theorem Algebra.etale_and_finite_of_isLocalHom {R R₁ S : Type*} [CommRing R] [CommRing R₁]
    [CommRing S] [Algebra R R₁] [Algebra R S] [IsLocalRing R] [IsLocalRing R₁]
    [Module.Flat R R₁] [IsLocalHom (algebraMap R R₁)]
    (hE : Algebra.Etale R₁ (R₁ ⊗[R] S)) (hF : Module.Finite R₁ (R₁ ⊗[R] S)) :
    Algebra.Etale R S ∧ Module.Finite R S := by
  have : Module.FaithfullyFlat R R₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat R₁,
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R₁⟩

/-- **Invariants and flat base change.** If the common fixed points of a finite family `σ` of
`S`-algebra endomorphisms of `L` are the elements of `S`, then for a flat `S`-algebra `T` the
common fixed points of the base changes `𝟙 ⊗ σᵢ` on `T ⊗[S] L` are the elements of `T`. -/
theorem AlgHom.mem_range_algebraMap_of_forall_baseChange_eq {S L T ι : Type*} [CommRing S]
    [CommRing L] [Algebra S L] [CommRing T] [Algebra S T] [Module.Flat S T] [_root_.Finite ι]
    (σ : ι → L →ₐ[S] L) (hfix : ∀ x, (∀ i, σ i x = x) → x ∈ Set.range (algebraMap S L))
    (y : T ⊗[S] L) (hy : ∀ i, Algebra.TensorProduct.map (AlgHom.id T T) (σ i) y = y) :
    y ∈ Set.range (algebraMap T (T ⊗[S] L)) := by
  let z := (AlgHom.tensorFixedPointsEquiv T σ).symm ⟨y, AlgHom.mem_fixedPoints.2 hy⟩
  have hz : (AlgHom.tensorFixedPointsEquiv T σ z : T ⊗[S] L) = y := by simp [z]
  have key (w : T ⊗[S] AlgHom.fixedPoints σ) :
      (AlgHom.tensorFixedPointsEquiv T σ w : T ⊗[S] L) ∈ Set.range (algebraMap T (T ⊗[S] L)) := by
    induction w with
    | zero => exact ⟨0, by simp⟩
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨a, ha⟩ := h₁
      obtain ⟨b, hb⟩ := h₂
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, Subalgebra.coe_add]⟩
    | tmul t a =>
      obtain ⟨s, hs⟩ := hfix a (AlgHom.mem_fixedPoints.1 a.2)
      refine ⟨s • t, ?_⟩
      rw [AlgHom.coe_tensorFixedPointsEquiv_tmul, ← hs, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
  rw [← hz]
  exact key z

/-- Let `A₁` be a discrete valuation ring which is an `R₀`-algebra, and `r₀ ∈ R₀` nonzero with
image in the maximal ideal of `A₁`. Then every nonzero element of `A₁` divides the image of a
nonzero element of `R₀`. -/
theorem IsDiscreteValuationRing.exists_dvd_algebraMap {R₀ A₁ : Type*} [CommRing R₀]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra R₀ A₁] {r₀ : R₀}
    (hr₀ : algebraMap R₀ A₁ r₀ ≠ 0) (hm : algebraMap R₀ A₁ r₀ ∈ IsLocalRing.maximalIdeal A₁)
    {a : A₁} (ha : a ≠ 0) : ∃ m : ℕ, a ∣ algebraMap R₀ A₁ (r₀ ^ m) ∧
      algebraMap R₀ A₁ (r₀ ^ m) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A₁
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hdvd : ϖ ∣ algebraMap R₀ A₁ r₀ := by
    rw [← Ideal.mem_span_singleton, ← (irreducible_iff_uniformizer ϖ).1 hϖ]
    exact hm
  refine ⟨m, ?_, by rw [map_pow]; exact pow_ne_zero m hr₀⟩
  rw [map_pow]
  exact (Units.mul_left_dvd.2 dvd_rfl).trans (pow_dvd_pow_of_dvd hdvd m)
