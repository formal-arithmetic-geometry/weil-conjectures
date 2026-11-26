/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# A normal ring is integrally closed in its total ring of fractions

`FractionRing R` is `Localization (nonZeroDivisors R)`, also for rings with zero divisors.
No domain assumption on `R` is made.

## Implementation details

Write `x = a / s`. For every prime `p`, normality of `R_p` puts `x` in `R_p`, so the ideal
`{r | r x ∈ R}` is not contained in `p`; hence it is the unit ideal.

## References

* [Stacks, Tag 034M]
-/

@[expose] public section

universe u

/-- Every element of the total ring of fractions of a normal commutative ring that is integral
over the ring comes from the ring. -/
theorem integral_totalFraction_mem_range_of_normal
    (R : Type u) [CommRing R]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R (FractionRing R) r = x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : a ∈ Ideal.span ({(s : R)} : Set R) := by
    apply Ideal.mem_of_localization_maximal
    intro p hp
    let : p.IsMaximal := hp
    let A := Localization.AtPrime p
    let K := FractionRing A
    let : IsDomain A := (hnormal p).1
    let : IsIntegrallyClosed A := (hnormal p).2
    let g : R →ₐ[R] K := Algebra.ofId R K
    have hu : ∀ t : nonZeroDivisors R, IsUnit (g t) := by
      intro t
      have ht : algebraMap R A t ∈ nonZeroDivisors A :=
        IsLocalization.nonZeroDivisors_le_comap p.primeCompl A t.2
      simpa only [g, Algebra.ofId_apply, IsScalarTower.algebraMap_apply R A K] using
        IsLocalization.map_units K (⟨algebraMap R A t, ht⟩ : nonZeroDivisors A)
    let f : FractionRing R →ₐ[R] K := IsLocalization.liftAlgHom hu
    have hi : IsIntegral A (f (IsLocalization.mk' (FractionRing R) a s)) :=
      (hx.map f).tower_top
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff K).mp inferInstance hi
    have he : algebraMap R A a = b * algebraMap R A s := by
      apply IsFractionRing.injective A K
      have hs := congrArg f (IsLocalization.mk'_spec (FractionRing R) a s)
      simpa only [map_mul, AlgHom.commutes, ← hb, g,
        IsScalarTower.algebraMap_apply R A K, map_mul] using hs.symm
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, he.trans (mul_comm _ _)⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, IsLocalization.eq_mk'_of_mul_eq ?_⟩
  exact (mul_comm _ _).trans hr.symm
