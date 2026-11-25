/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.RingTheory.PopescuDesingularizationQuotientData
import WeilConjectures.RingTheory.QuadraticRelationsSmoothQuotient
import Mathlib.RingTheory.FiniteType

/-!
# The desingularization lemma

If `π` is strictly standard in `A` over `R` and `A → Λ` admits a compatible section modulo `π⁴`,
then the map factors through a finitely presented algebra which is smooth outside the zero locus
of the extended annihilator ideal.

## Implementation details

After translating the variables, the substitution `xᵢ = π² ∑ sᵢₖ vₖ + π³ wᵢ` with a scalar left
inverse `s` gives `fⱼ = π³ gⱼ`; the algebra is `B = R[x, v, w] / (f, h, g)`. After inverting `π`,
`B_π ≅ A_π[v]` is smooth. At primes containing `π`, `B' = R[v, w] / (g)` is smooth by the flat
smooth-fibre criterion, and outside the annihilator ideal the remaining relations vanish locally
by the Krull intersection theorem, so `B` agrees with `B'` there.

## References

* [Stacks, Tag 07CR]
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Desingularization with a compatible section modulo the fourth power of a strictly
standard element `π`: the map `A → Λ` factors through a finitely presented algebra whose
singular ideal contains the extension of the annihilator ideal. Compatibility is tested on
representatives: if `ρ` sends the class of `a` to the class of `r`, their images in `Λ / π⁴Λ`
agree. Being an `R`-algebra map, `ρ` automatically retracts the structural map from `R / π⁴R`. -/
theorem exists_desingularization
    (R : Type u) (Λ : Type v) (A : Type w)
    [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [IsNoetherianRing R] [FinitePresentation R A]
    (π : R) (α : A →ₐ[R] Λ)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hρ : ∃ ρ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (R ⧸ Ideal.span {π ^ 4}),
      ∀ (a : A) (r : R),
        ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (algebraMap R Λ r)) :
    ∃ (B : Type (max u w)) (_ : CommRing B) (_ : Algebra R B),
      FinitePresentation R B ∧
      ∃ (β : B →ₐ[R] Λ) (aB : A →ₐ[R] B),
        β.comp aB = α ∧
        Ideal.span ((algebraMap R B) ''
          {r : R | ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0}) ≤ singularIdeal R B := by
  obtain ⟨S, instS, algS, hSfp, K, hdiv, hquad, hBfp, β, aB, hcomp, haway, hlocal⟩ :=
    exists_desingularization_quotient_data R Λ A π α hΛ hstandard hρ
  let : CommRing S := instS
  let : Algebra R S := algS
  let : FinitePresentation R S := hSfp
  let : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  refine ⟨S ⧸ K, inferInstance, inferInstance, hBfp, β, aB, hcomp, ?_⟩
  let J : Ideal (S ⧸ K) := Ideal.span ((algebraMap R (S ⧸ K)) ''
    {r : R | ∀ x : R, π ^ 2 * x = 0 → r * π * x = 0})
  have hV : PrimeSpectrum.zeroLocus (singularIdeal R (S ⧸ K) : Set (S ⧸ K)) ⊆
      PrimeSpectrum.zeroLocus (J : Set (S ⧸ K)) := by
    intro q hq
    have hnsm : ¬ IsSmoothAtPrime R q := by
      rw [(singularIdeal_zeroLocus R (S ⧸ K)).1] at hq
      exact hq
    change J ≤ q.asIdeal
    apply Ideal.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    by_contra hrq
    apply hnsm
    by_cases hπ : algebraMap R (S ⧸ K) π ∈ q.asIdeal
    · have hπ' : algebraMap R S π ∈
          (PrimeSpectrum.comap (Ideal.Quotient.mk K) q).asIdeal := hπ
      obtain ⟨hsm, hflat⟩ := hlocal _ hπ'
      exact smoothAtPrime_quotient_of_quadratic_relations π K hdiv hquad q hπ
        hsm hflat r hr hrq
    · exact ⟨algebraMap R (S ⧸ K) π, hπ, haway⟩
  have hle := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
    (singularIdeal R (S ⧸ K)) J).mp hV
  exact hle.trans (singularIdeal_isRadical R (S ⧸ K)).radical.le

end Algebra
