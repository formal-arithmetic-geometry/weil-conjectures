/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.PopescuDesingularizeLiftingApply
import WeilConjectures.RingTheory.PopescuIdealCompEquiv
import WeilConjectures.RingTheory.SingularIdealMapEquiv
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.StrictlyStandardElement

/-!
# Lifting a Popescu resolution for one element

We prove the one-element case of the lifting step for Popescu resolutions.

## Implementation details

The resolving algebra is represented by a finite polynomial presentation over `R`, so that its
carrier lies in the universe required by `CanBePopescuResolved`.

## References

* [Stacks, Lemma 07F8] (case `r = 1`, using [Stacks, Lemma 07F0])
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Equality of multiplication kernels gives equality of the annihilators of the
principal ideals. -/
private theorem ann_span_eq_of_mul_iff
    {S : Type*} [CommRing S] (a b : S) (h : ∀ x : S, a * x = 0 ↔ b * x = 0) :
    Module.annihilator S (Ideal.span ({a} : Set S)) =
      Module.annihilator S (Ideal.span ({b} : Set S)) := by
  ext x
  change x ∈ (Ideal.span ({a} : Set S)).annihilator ↔
    x ∈ (Ideal.span ({b} : Set S)).annihilator
  simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm] using h x

/-- If `R_π → B_π` is smooth, then the image of `π` lies in the singular ideal of `B`. -/
private theorem parameter_mem_singular
    {R : Type*} {B : Type*} [CommRing R] [CommRing B] [Algebra R B] (π : R)
    (hs : @Smooth (Localization.Away π) _ (Localization.Away (algebraMap R B π)) _
      (Localization.awayMap (algebraMap R B) π).toAlgebra) :
    algebraMap R B π ∈ singularIdeal R B := by
  let : Algebra (Localization.Away π) (Localization.Away (algebraMap R B π)) :=
    (Localization.awayMap (algebraMap R B) π).toAlgebra
  have : IsScalarTower R (Localization.Away π)
      (Localization.Away (algebraMap R B π)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change (algebraMap B _ (algebraMap R B r)) =
        Localization.awayMap (algebraMap R B) π (algebraMap R _ r)
      simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have : Smooth R (Localization.Away π) := Smooth.of_isLocalization_Away π
  have : Smooth (Localization.Away π) (Localization.Away (algebraMap R B π)) := hs
  have : Smooth R (Localization.Away (algebraMap R B π)) :=
    Smooth.comp R (Localization.Away π) _
  exact Ideal.le_radical (Ideal.subset_span (show algebraMap R B π ∈ smoothElements R B
    from show Smooth R (Localization.Away (algebraMap R B π)) from inferInstance))

/-- Singular ideals map into singular ideals after quotient base change. -/
private theorem singular_quotient_le
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A] (J : Ideal R) :
    Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) J)) (singularIdeal R A) ≤
      singularIdeal (R ⧸ J) (A ⧸ Ideal.map (algebraMap R A) J) := by
  let T := TensorProduct R (R ⧸ J) A
  let f : A →ₐ[R] T := TensorProduct.includeRight
  have hbase : Ideal.map f.toRingHom (singularIdeal R A) ≤ singularIdeal (R ⧸ J) T := by
    unfold singularIdeal
    refine (Ideal.map_radical_le f.toRingHom).trans (Ideal.radical_mono ?_)
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    intro a ha
    apply Ideal.subset_span
    change Smooth (R ⧸ J) (Localization.Away (f a))
    have : Smooth R (Localization.Away a) := ha
    have : Smooth (R ⧸ J) (TensorProduct R (R ⧸ J) (Localization.Away a)) := inferInstance
    exact Smooth.of_equiv
      (IsLocalization.Away.tensorProductEquivTMulRight R (R ⧸ J) a (Localization.Away a))
  let e := TensorProduct.quotIdealMapEquivQuotTensor A J
  have he : e.symm.toRingHom.comp f.toRingHom =
      Ideal.Quotient.mk (Ideal.map (algebraMap R A) J) := by
    ext a
    apply e.injective
    simp [e, f]
    rfl
  rw [← he, ← Ideal.map_map]
  exact (Ideal.map_mono hbase).trans (singularIdeal_map_equiv_le e.symm)

/-- A resolution through a finitely presented intermediate algebra can be transported to a
finite polynomial quotient in the required universe. -/
private theorem resolution_resize
    {R : Type u} {A : Type v} {Λ : Type w} {B : Type*}
    [CommRing R] [CommRing A] [CommRing Λ] [CommRing B]
    [Algebra R A] [Algebra R Λ] [Algebra R B]
    [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (aB : A →ₐ[R] B) (β : B →ₐ[R] Λ) (h : IsPopescuResolution α q aB β) :
    CanBePopescuResolved α q := by
  have : FinitePresentation R B := h.1
  obtain ⟨n, I, e, hI⟩ := FinitePresentation.iff.mp (inferInstance : FinitePresentation R B)
  let D := ULift.{v} (MvPolynomial (Fin n) R ⧸ I)
  let eD : D ≃ₐ[R] B := ULift.algEquiv.trans e
  have : FinitePresentation R D := FinitePresentation.equiv eD.symm
  refine ⟨D, inferInstance, inferInstance, eD.symm.toAlgHom.comp aB,
    β.comp eD.toAlgHom, inferInstance, ?_, ?_, ?_⟩
  · ext x
    change β (eD (eD.symm (aB x))) = α x
    rw [eD.apply_symm_apply]
    exact AlgHom.congr_fun h.2.1 x
  · simpa only [popescuIdeal_comp_equiv] using h.2.2.1
  · simpa only [popescuIdeal_comp_equiv] using h.2.2.2

/-- The one-element case of lifting a resolution. -/
theorem popescuEighthPowerLifting_one : PopescuEighthPowerLifting.{u, v, w} 1 := by
  intro R A Λ _ _ _ _ _ _ _ π α q hq hAnnR hAnnΛ hstandard hresolved
  have hR0 := hAnnR 0
  have hΛ0 := hAnnΛ 0
  have hprevR : Ideal.span
      {y : R | ∃ j : Fin 1, j.val < (0 : Fin 1).val ∧ y = π j ^ 8} = ⊥ := by
    have hset : {y : R | ∃ j : Fin 1, j.val < (0 : Fin 1).val ∧ y = π j ^ 8} =
        ∅ := by ext; simp
    rw [hset, Ideal.span_empty]
  have hprevΛ : Ideal.span
      {y : Λ | ∃ j : Fin 1, j.val < (0 : Fin 1).val ∧
        y = algebraMap R Λ (π j) ^ 8} = ⊥ := by
    have hset : {y : Λ | ∃ j : Fin 1, j.val < (0 : Fin 1).val ∧
        y = algebraMap R Λ (π j) ^ 8} = ∅ := by ext; simp
    rw [hset, Ideal.span_empty]
  rw [hprevR] at hR0
  rw [hprevΛ] at hΛ0
  have hR : Module.annihilator R (Ideal.span ({π 0} : Set R)) =
      Module.annihilator R (Ideal.span ({π 0 ^ 2} : Set R)) := by
    apply ann_span_eq_of_mul_iff
    intro x
    have h := hR0 (Ideal.Quotient.mk ⊥ x)
    change Ideal.Quotient.mk ⊥ (π 0 * x) = 0 ↔
      Ideal.Quotient.mk ⊥ (π 0 ^ 2 * x) = 0 at h
    simpa only [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_bot] using h
  have hΛ : Module.annihilator Λ (Ideal.span ({algebraMap R Λ (π 0)} : Set Λ)) =
      Module.annihilator Λ (Ideal.span ({algebraMap R Λ (π 0) ^ 2} : Set Λ)) := by
    apply ann_span_eq_of_mul_iff
    intro x
    have h := hΛ0 (Ideal.Quotient.mk ⊥ x)
    have hm (r : R) : r • Ideal.Quotient.mk (⊥ : Ideal Λ) x =
        Ideal.Quotient.mk (⊥ : Ideal Λ) (r • x) :=
      (map_smul (Ideal.Quotient.mkₐ R (⊥ : Ideal Λ)) r x).symm
    rw [hm, hm] at h
    simpa only [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_bot,
      Algebra.smul_def, map_pow] using h
  have hJ : Ideal.span (Set.range (fun i : Fin 1 ↦ π i ^ 8)) =
      Ideal.span ({π 0 ^ 8} : Set R) := by
    congr 1
    ext x
    simp [eq_comm]
  unfold PopescuEighthPowerQuotientResolved at hresolved
  dsimp only at hresolved
  rw [hJ] at hresolved
  obtain ⟨hfp, α₀, q₀, hcomm, hprime, C, hC, hRC, σ, τ, hres⟩ := hresolved
  have : FinitePresentation (R ⧸ Ideal.span ({π 0 ^ 8} : Set R)) C := hres.1
  obtain ⟨B, hB, hRB, hfpB, β, aB, hfactor, hsmooth, hsing⟩ :=
    popescu_desingularize_lifting_apply R A Λ (π 0) hR hΛ α (hstandard 0) C σ τ
      (fun a ↦ (AlgHom.congr_fun hres.2.1 _).trans (RingHom.congr_fun hcomm a))
  let J := Ideal.span ({π 0 ^ 8} : Set R)
  let K := Ideal.map (algebraMap R Λ) J
  let p := Ideal.Quotient.mk K
  let L := popescuIdeal β
  have hπ : algebraMap R Λ (π 0) ∈ L := by
    rw [← β.commutes]
    exact Ideal.le_radical
      (Ideal.mem_map_of_mem β.toRingHom (parameter_mem_singular (π 0) hsmooth))
  have hK : K ≤ L := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl : x = π 0 ^ 8 := hx
    change algebraMap R Λ (π 0 ^ 8) ∈ L
    rw [map_pow]
    exact Ideal.pow_mem_of_mem L hπ 8 (by decide)
  have hker : RingHom.ker p ≤ L := by
    simpa only [p, Ideal.mk_ker] using hK
  have hrad : (Ideal.map p L).radical = Ideal.map p L := by
    rw [← Ideal.map_radical_of_surjective (Ideal.Quotient.mk_surjective) hker]
    exact congrArg (Ideal.map p) (Ideal.radical_isRadical _).radical
  have hpre : Ideal.comap p (Ideal.map p L) = L := by
    rw [Ideal.comap_map_of_surjective p Ideal.Quotient.mk_surjective]
    exact sup_eq_left.mpr hker
  have hτ : popescuIdeal τ ≤ Ideal.map p L := by
    exact (Ideal.radical_mono hsing).trans_eq hrad
  have hα : Ideal.map p (popescuIdeal α) ≤ popescuIdeal α₀ := by
    unfold popescuIdeal
    refine (Ideal.map_radical_le p).trans (Ideal.radical_mono ?_)
    rw [Ideal.map_map]
    change Ideal.map (p.comp α.toRingHom) (singularIdeal R A) ≤ _
    rw [← hcomm, ← Ideal.map_map]
    exact Ideal.map_mono (singular_quotient_le J)
  have hincl : popescuIdeal α ≤ L := by
    rw [← hpre]
    exact Ideal.map_le_iff_le_comap.mp (hα.trans (hres.2.2.1.trans hτ))
  have hnot : ¬ L ≤ q.asIdeal := by
    intro hh
    apply hres.2.2.2
    refine hτ.trans (Ideal.map_le_iff_le_comap.mpr ?_)
    change L ≤ (PrimeSpectrum.comap p q₀).asIdeal
    dsimp only [p, K, J]
    rw [hprime]
    exact hh
  exact resolution_resize α q aB β ⟨hfpB, hfactor, hincl, hnot⟩

end Algebra
