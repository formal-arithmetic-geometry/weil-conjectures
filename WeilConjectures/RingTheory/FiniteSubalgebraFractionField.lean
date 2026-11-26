/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite subalgebras with prescribed fraction field

For `A = k[[x₁, …, xₙ]][y₁, …, yₘ]`, every finite extension of the fraction field of `A` is the
fraction field of a finite `A`-subalgebra.

## Main results

* `MvPolynomial.exists_finite_subalgebra_fraction_field`

## Implementation details

`FiniteDimensional.exists_is_basis_integral` gives a basis `e` of `M` over `K` consisting of
elements integral over `A`, and `B = Algebra.adjoin A (Set.range e)` is finite over `A`.
Clearing the denominators of the coordinates of `z ∈ M` with
`IsLocalization.exist_integer_multiples_of_finite` writes `z = (d • z) / d` with
`d • z, d ∈ B`. No separability or Dedekind hypothesis is needed.

## References

* [Stacks, Tag 07PR] (finite algebra model paragraph of the proof)
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- For `A = k[[x₁, …, xₙ]][y₁, …, yₘ]` in positive characteristic, `A` is a domain and
any finite extension `M` of its fraction field has a finite `A`-subalgebra with fraction
field `M`. The scalar tower identifies the structural map `A → M` with `A → K → M`. -/
theorem exists_finite_subalgebra_fraction_field
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsLocalization.AtPrime K
      (⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))]
    (M : Type w) [Field M] [Algebra K M]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M]
    [IsScalarTower (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K M]
    [Module.Finite K M] :
    IsDomain (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ∧
      ∃ B : Subalgebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M,
        Module.Finite (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) B ∧
          ∀ z : M, ∃ b s : B, (s : M) ≠ 0 ∧ z = (b : M) / (s : M) := by
  classical
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  have hA : IsDomain A := inferInstance
  have : IsFractionRing A K := by
    simpa only [IsLocalization.AtPrime, Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization.AtPrime K (⊥ : Ideal A))
  have _hp := hp
  refine ⟨hA, ?_⟩
  obtain ⟨t, e, he⟩ := FiniteDimensional.exists_is_basis_integral A K M
  let B := Algebra.adjoin A (Set.range e)
  have hB : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range e)
      (by rintro _ ⟨i, rfl⟩; exact he i)
  refine ⟨B, hB, ?_⟩
  intro z
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) (fun i => e.repr z i)
  choose a ha using hd
  have hd0 : (d : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdm : algebraMap A M d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K M]
    exact (map_ne_zero (algebraMap K M)).mpr
      ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hd0)
  have hdz : (d : A) • z ∈ B := by
    rw [← e.sum_repr z, Finset.smul_sum]
    apply B.sum_mem
    intro i _
    rw [← smul_assoc, ← ha i, algebraMap_smul]
    exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
  refine ⟨⟨(d : A) • z, hdz⟩, ⟨algebraMap A M d, B.algebraMap_mem d⟩, hdm, ?_⟩
  change z = ((d : A) • z) / algebraMap A M d
  rw [Algebra.smul_def, mul_div_cancel_left₀ _ hdm]

end MvPolynomial
