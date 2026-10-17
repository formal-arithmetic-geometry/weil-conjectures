/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import WeilConjectures.RingTheory.Smooth.IntegrallyClosed

/-!
# The generic points of the closed fibre of a smooth algebra over a trait

Let `A` be a discrete valuation ring with uniformizer `ϖ` and `B` a smooth `A`-algebra. The local
ring of `B` at a generic point of the closed fibre (a minimal prime of `ϖB`) is a discrete
valuation ring with uniformizer `ϖ`
(`Algebra.Smooth.isDiscreteValuationRing_localization_of_mem_minimalPrimes`): the closed fibre
is smooth over the residue field, hence reduced.

We also record that minimal primes descend along maps with going down
(`Ideal.comap_mem_minimalPrimes_of_le_radical`).

This is used in the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

/-- **Minimal primes descend along going down.** Let `R → S` satisfy going down, `I ⊆ R` and
`J ⊆ S` ideals with `IS ⊆ J ⊆ √(IS)`. Then the contraction of a minimal prime of `J` is a minimal
prime of `I`. -/
theorem Ideal.comap_mem_minimalPrimes_of_le_radical {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] {I : Ideal R} {J : Ideal S}
    (hIJ : I.map (algebraMap R S) ≤ J) (hJ : J ≤ (I.map (algebraMap R S)).radical) {Q : Ideal S}
    (hQ : Q ∈ J.minimalPrimes) : Q.comap (algebraMap R S) ∈ I.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.1.1
  refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.1 (hIJ.trans hQ.1.2)⟩,
    fun ⦃q⦄ ⟨hq, hIq⟩ hqQ ↦ ?_⟩
  have : Q.LiesOver (Q.comap (algebraMap R S)) := ⟨rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hqQ
  have hIQ' : I.map (algebraMap R S) ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← hlies.over]
    exact hIq
  have hJQ' : J ≤ Q' := hJ.trans (hQ'.radical_le_iff.2 hIQ')
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ', hJQ'⟩ hQ'Q
  rw [hlies.over, Ideal.under_def]
  exact Ideal.comap_mono hQQ'

namespace Algebra.Smooth

variable {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
  [Algebra A B] [Algebra.Smooth A B]

/-- The closed fibre `B ⧸ 𝔪B` of a smooth algebra over a discrete valuation ring is reduced. -/
theorem isRadical_map_maximalIdeal : ((maximalIdeal A).map (algebraMap A B)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let := Ideal.Quotient.field (maximalIdeal A)
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ maximalIdeal A)).toRingEquiv
  have : IsReduced ((A ⧸ maximalIdeal A) ⊗[A] B) :=
    Algebra.Smooth.isReduced_of_field (A ⧸ maximalIdeal A) _
  exact isReduced_of_injective e.toRingHom e.injective

/-- **The generic points of the closed fibre.** The localization of a smooth algebra `B` over a
discrete valuation ring `A` at a minimal prime of `𝔪B` is a discrete valuation ring, with
uniformizer the image of a uniformizer `ϖ` of `A`. -/
theorem isDiscreteValuationRing_localization_of_mem_minimalPrimes {ϖ : A} (hϖ : Irreducible ϖ)
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮 : 𝔮 ∈ ((maximalIdeal A).map (algebraMap A B)).minimalPrimes) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔮), IsDiscreteValuationRing (Localization.AtPrime 𝔮) ∧
      Irreducible (algebraMap A (Localization.AtPrime 𝔮) ϖ) := by
  let O := Localization.AtPrime 𝔮
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsNoetherianRing O := IsLocalization.isNoetherianRing 𝔮.primeCompl O inferInstance
  obtain ⟨hdom, -⟩ := Algebra.Smooth.isDomain_and_isIntegrallyClosed_localization A B 𝔮
  have hJ : ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B O) =
      Ideal.span {algebraMap A O ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  have hm : maximalIdeal O = ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B O) := by
    refine le_antisymm ?_ ?_
    · rw [← (isRadical_map_maximalIdeal (A := A) (B := B)).radical,
        IsLocalization.map_radical 𝔮.primeCompl O, Ideal.radical_eq_sInf]
      refine le_sInf fun p ⟨hJp, hp⟩ ↦ ?_
      have hle : p.comap (algebraMap B O) ≤ 𝔮 :=
        (Ideal.comap_mono (le_maximalIdeal hp.ne_top)).trans
          (Localization.AtPrime.under_maximalIdeal (I := 𝔮)).le
      have hcomap : p.comap (algebraMap B O) = 𝔮 :=
        le_antisymm hle (h𝔮.2 ⟨hp.comap _, Ideal.map_le_iff_le_comap.1 hJp⟩ hle)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact (Ideal.map_mono hcomap.ge).trans Ideal.map_comap_le
    · rw [Ideal.map_le_iff_le_comap]
      exact h𝔮.1.2.trans (Localization.AtPrime.under_maximalIdeal (I := 𝔮)).ge
  have : Module.Flat A O := Module.Flat.trans A B O
  have hϖ0 : algebraMap A O ϖ ≠ 0 := by
    intro h
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := O)
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    refine one_ne_zero (hreg (?_ : ϖ • (1 : O) = ϖ • 0))
    rw [Algebra.smul_def, h, smul_zero, zero_mul]
  rw [hJ] at hm
  exact ⟨hdom, IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton hϖ0 hm,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖ0 hm⟩

end Algebra.Smooth
