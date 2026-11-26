/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FiniteProductNormal
import WeilConjectures.RingTheory.IntegralClosureFinitePi
import Mathlib.RingTheory.Localization.Pi
import WeilConjectures.RingTheory.IntegrallyClosedReducedFiniteDomainDecomposition
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal

/-!
# Normality and total fractions of a reduced ring

For a reduced ring with finitely many minimal primes, normality, integral closedness in the
total ring of fractions, and being a finite product of normal domains are equivalent.

## Implementation details

`FractionRing R` is localization at `nonZeroDivisors R`. Normality is the prime-localization
condition. The empty finite product is allowed.

The total fraction ring `Q(R)` is reduced, its primes are the minimal primes, and it is the
product of the fields `R_p`. Normality implies integral closedness since an integral total
fraction lies locally in every `R_p`. If `R` is integrally closed in `Q(R)`, the coordinate
idempotents (roots of `T^2 - T`) lie in `R` and decompose it into the domains `R/p`, each
integrally closed in its fraction field `R_p`. A finite product of normal domains is normal.

## References

* [Stacks, Tag 030C]
-/

@[expose] public section

universe u

private theorem nonZeroDivisors_pi {I : Type*} (A : I → Type u)
    [∀ i, CommRing (A i)] :
    nonZeroDivisors (∀ i, A i) = Submonoid.pi Set.univ (fun i ↦ nonZeroDivisors (A i)) := by
  classical
  ext x
  change x ∈ nonZeroDivisors (∀ i, A i) ↔ ∀ i, i ∈ Set.univ →
    x i ∈ nonZeroDivisors (A i)
  simp only [Set.mem_univ, forall_const]
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro hx i y hy
    have hxy : Pi.single i y * x = 0 := by
      ext j
      by_cases hji : j = i
      · subst j
        simpa using hy
      · simp [Pi.single_eq_of_ne hji]
    have hz := hx (Pi.single i y) hxy
    simpa using congrFun hz i
  · intro hx y hy
    ext i
    exact hx i (y i) (congrFun hy i)

private theorem integrallyClosed_factors {I : Type*} [Finite I] (A : I → Type u)
    [∀ i, CommRing (A i)] (h : IsIntegrallyClosed (∀ i, A i)) :
    ∀ i, IsIntegrallyClosed (A i) := by
  let : IsLocalization (nonZeroDivisors (∀ i, A i)) (∀ i, FractionRing (A i)) := by
    rw [nonZeroDivisors_pi A]
    infer_instance
  have hc : IsIntegrallyClosedIn (∀ i, A i) (∀ i, FractionRing (A i)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (∀ i, FractionRing (A i))).mp h
  have hi := (integralClosure_finite_pi A (fun i ↦ FractionRing (A i))
    (fun i ↦ algebraMap (A i) (FractionRing (A i)))).2
      (fun i ↦ IsFractionRing.injective (A i) (FractionRing (A i)))
  have hφ : (fun i ↦ (algebraMap (A i) (FractionRing (A i))).toAlgebra) =
      (fun i ↦ inferInstanceAs (Algebra (A i) (FractionRing (A i)))) := by
    funext i
    exact toAlgebra_algebraMap
  rw [hφ] at hi
  exact hi.mp hc

/-- For a reduced ring with finitely many minimal primes, normality, integral closedness
in the total fraction ring, and being a finite product of normal domains are equivalent. -/
theorem reduced_normal_iff_integrallyClosed_totalFractions
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    ((∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      IsIntegrallyClosedIn R (FractionRing R)) ∧
    (IsIntegrallyClosedIn R (FractionRing R) ↔
      ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
        (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
          Nonempty (R ≃+* (∀ i : Fin n, A i))) := by
  have normal_to_closed (hn : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
      IsIntegrallyClosedIn R (FractionRing R) := by
    exact (isIntegrallyClosed_iff (FractionRing R)).mpr
      (fun {x} hx ↦ integral_totalFraction_mem_range_of_normal R hn x hx)
  have closed_to_product (hc : IsIntegrallyClosedIn R (FractionRing R)) :
      ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
        (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
          Nonempty (R ≃+* (∀ i : Fin n, A i)) := by
    obtain ⟨n, A, hA, ⟨e⟩⟩ :=
      exists_finite_domain_factors_of_integrallyClosed_totalFractions R hfinite hc
    have hp : IsIntegrallyClosed (∀ i : Fin n, A i) :=
      IsIntegrallyClosed.of_equiv e
    exact ⟨n, A, fun i ↦ ⟨hA i, integrallyClosed_factors (fun i ↦ (A i : Type u)) hp i⟩, ⟨e⟩⟩
  have product_to_normal
      (hp : ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
        (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
          Nonempty (R ≃+* (∀ i : Fin n, A i))) :
      ∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    obtain ⟨n, A, hA, ⟨e⟩⟩ := hp
    have hf : ∀ (i : Fin n) (p : Ideal (A i)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
      intro i p hprime
      let : IsDomain (A i) := (hA i).1
      let : IsIntegrallyClosed (A i) := (hA i).2
      exact ⟨inferInstance,
        isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
          p.primeCompl_le_nonZeroDivisors⟩
    intro p hprime
    let q : Ideal (∀ i : Fin n, A i) := p.comap e.symm
    let : q.IsPrime := inferInstance
    obtain ⟨hd, hc⟩ := Pi.isNormalRing_of_finite (fun i ↦ A i) hf q
    let el := Localization.localRingEquiv p q e (by
      dsimp [q]
      exact (Ideal.comap_of_equiv e (I := p)).symm)
    let : IsIntegrallyClosed (Localization.AtPrime q) := hc
    exact ⟨el.toMulEquiv.isDomain_iff.mpr hd, IsIntegrallyClosed.of_equiv el.symm⟩
  exact ⟨⟨normal_to_closed, fun hc ↦ product_to_normal (closed_to_product hc)⟩,
    ⟨closed_to_product, fun hp ↦ normal_to_closed (product_to_normal hp)⟩⟩
