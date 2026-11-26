/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.RingTheory.EssentiallySmoothLocalizedQuotientFactorization

/-!
# Popescu characteristic-p preparation: quotient descent

The auxiliary thickening factorization of the positive characteristic case descends to the
quotient by the eighth powers of the parameters.

## Implementation details

The quotient by `J = (π_i^8)` is finitely presented, and the maximal-ideal power bound makes the
image of `q` a minimal prime of `Λ / J Λ`; this bound is needed because zero parameters alone
would not cut the localization down to dimension zero. The factorization itself comes from
`essentiallySmooth_localized_quotient_factorization`.

## References

* [Stacks, Tag 07FJ] (construction and quotient steps)
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

set_option linter.unusedVariables false in
/-- Descend the auxiliary thickening factorization to the eighth-power quotient and derive
the dimension and minimal-prime alternative. -/
theorem popescu_char_p_preparation_quotient
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (m : ℕ) [Algebra (MvPolynomial (Fin m) k) Λ]
      [IsScalarTower k (MvPolynomial (Fin m) k) Λ]
    (C : Type (max u v)) [CommRing C] [Algebra k C]
      [Algebra (MvPolynomial (Fin m) k) C]
      [IsScalarTower k (MvPolynomial (Fin m) k) C]
      [FinitePresentation (MvPolynomial (Fin m) k) C]
    (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ)
    (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k)
    (hbase : (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ)
    (hparam : 1 ≤ r ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin r)
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin r)
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ i, IsStrictlyStandardElement
        (R := MvPolynomial (Fin m) k)
        (algebraMap (MvPolynomial (Fin m) k) C (π i))))
    (hconstruction :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ))
              (fun _ _ ↦ Commute.all _ _)) :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let J_C := J.map (algebraMap R C)
    let J_Λ := J.map (algebraMap R Λ)
    let R₀ := R ⧸ J
    let C₀ := C ⧸ J_C
    let Λ₀ := Λ ⧸ J_Λ
    ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
      (q₀ : PrimeSpectrum Λ₀),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
        q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
        ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
        let P := Localization.AtPrime (q₀.asIdeal.under R₀)
        let L := Localization.AtPrime q₀.asIdeal
        letI := Localization.AtPrime.algebraOfLiesOver
          (q₀.asIdeal.under R₀) q₀.asIdeal
        ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
          EssentiallySmooth P E ∧
          ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
              ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
              (fun _ _ ↦ Commute.all _ _)) := by
  classical
  let R := MvPolynomial (Fin m) k
  let J : Ideal R := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
  let JC := J.map (algebraMap R C)
  let JT := J.map (algebraMap R Λ)
  have hJT : JT ≤ q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change algebraMap R Λ (π i ^ 8) ∈ q.asIdeal
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ (hparam.2.1 i) 8 (by decide)
  have hJC : JC ≤ JT.comap γ.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change γ (algebraMap R C x) ∈ JT
    rw [γ.commutes]
    exact Ideal.mem_map_of_mem _ hx
  let γR := Ideal.quotientMapₐ JT γ hJC
  let γ₀ : (C ⧸ JC) →ₐ[R ⧸ J] (Λ ⧸ JT) :=
    { γR.toRingHom with
      commutes' := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp [γR, JC, JT] }
  have hqprime : (q.asIdeal.map (Ideal.Quotient.mk JT)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hJT
  let q₀ : PrimeSpectrum (Λ ⧸ JT) := ⟨_, hqprime⟩
  have hq : PrimeSpectrum.comap (Ideal.Quotient.mk JT) q₀ = q := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_map_mk hJT
  have hfpR : FinitePresentation R (C ⧸ JC) :=
    FinitePresentation.quotient
      (Ideal.FG.map (Submodule.fg_span (Set.finite_range _)) (algebraMap R C))
  have hfp : FinitePresentation (R ⧸ J) (C ⧸ JC) :=
    FinitePresentation.of_restrict_scalars_finitePresentation R (R ⧸ J) (C ⧸ JC)
  refine ⟨hfp, γ₀, q₀, ?_, hq, ?_⟩
  · ext x
    rfl
  · obtain ⟨n, hn, hpow, hfactor⟩ := hconstruction
    by_cases hH : popescuIdeal γ₀ ≤ q₀.asIdeal
    · right
      have hminimal : q₀.asIdeal ∈ minimalPrimes (Λ ⧸ JT) := by
        refine ⟨⟨q₀.isPrime, bot_le⟩, ?_⟩
        intro p₀ hp₀ hpq₀
        have : p₀.IsPrime := hp₀.1
        let p := p₀.comap (Ideal.Quotient.mk JT)
        have hpq : p ≤ q.asIdeal := by
          change Ideal.comap (Ideal.Quotient.mk JT) p₀ ≤ q.asIdeal
          rw [← hq]
          exact Ideal.comap_mono hpq₀
        have hpJT : JT ≤ p := by
          intro x hx
          change Ideal.Quotient.mk JT x ∈ p₀
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact p₀.zero_mem
        let L := Localization.AtPrime q.asIdeal
        have hpL : (p.map (algebraMap Λ L)).IsPrime :=
          Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal hpq
        have hm : IsLocalRing.maximalIdeal L ≤ p.map (algebraMap Λ L) :=
          Ideal.IsPrime.le_of_pow_le (hpow.trans (Ideal.map_mono hpJT))
        have hqp : q.asIdeal ≤ p := by
          calc
            q.asIdeal = (IsLocalRing.maximalIdeal L).under Λ :=
              (IsLocalization.AtPrime.under_maximalIdeal L q.asIdeal).symm
            _ ≤ (p.map (algebraMap Λ L)).under Λ := Ideal.comap_mono hm
            _ = p := Ideal.under_map_of_isLocalizationAtPrime q.asIdeal (S := L) hpq
        have hq₀p₀ : q₀.asIdeal ≤ p₀ := by
          rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk JT)
            Ideal.Quotient.mk_surjective p₀]
          exact Ideal.map_mono hqp
        exact hq₀p₀
      have hdim : ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 := by
        have : Ring.KrullDimLE 0 (Localization.AtPrime q₀.asIdeal) :=
          Ring.KrullDimLE.of_isLocalization q₀.asIdeal hminimal _
        exact (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp inferInstance
      refine ⟨⟨⟨q₀.isPrime, hH⟩, fun p hp hpq ↦ hminimal.2 ⟨hp.1, bot_le⟩ hpq⟩,
        hdim, ?_⟩
      exact essentiallySmooth_localized_quotient_factorization γ q J γ₀ q₀
        (by ext x; rfl) hq hfactor
    · exact Or.inl hH

end Algebra
