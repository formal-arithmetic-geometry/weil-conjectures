/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximumCore
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite data for the dimensions of minimal components

The minimal primes below a prime `p` of a finite type algebra over a field are finite and
nonempty; the maximal dimension of the corresponding components is `dim S_p + trdeg κ(p)`.

## Implementation details

Prime correspondence in the localization identifies chains below `p` with chains in `S_p`.
Concatenating with a maximal chain above `p` of length `trdeg κ(p)` gives the dimension of a
component attaining the maximum, and bounds every other component.

## References

* [Stacks, Tag 00P1] (proof)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Auxiliary finite-component form of the prime-chain dimension argument.
-/
theorem minimal_component_dimension_maximum_data
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∃ qs : Finset (Ideal S),
      (∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
        (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q)) ∧
      qs.Nonempty ∧
      ((∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞)) ∧
        (∃ q ∈ qs, ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞))) := by
  classical
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let T : Set (Ideal S) := {q | q ∈ minimalPrimes S ∧ q ≤ p}
  have hT : T.Finite := (minimalPrimes.finite_of_isNoetherianRing S).subset
    (fun _ h ↦ h.1)
  let qs := hT.toFinset
  have hqs : ∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
      ∀ t : Ideal S, t.IsPrime → t ≤ q → t = q := by
    intro q
    simp only [qs, Set.Finite.mem_toFinset, T, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hqp⟩
      exact ⟨hq.isPrime, hqp, fun t ht htq ↦
        le_antisymm htq (hq.2 ⟨ht, bot_le⟩ htq)⟩
    · rintro ⟨hq, hqp, hmin⟩
      exact ⟨⟨⟨hq, bot_le⟩, fun t ht htq ↦ (hmin t ht.1 htq).ge⟩, hqp⟩
  have hne : qs.Nonempty := by
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S))
      (J := p) bot_le
    exact ⟨q, hT.mem_toFinset.mpr ⟨hq, hqp⟩⟩
  have hbound := minimal_component_dimension_maximum_bound (k := k) p d r hd hr
  have hattain := minimal_component_dimension_maximum_attained (k := k) p d r hd hr
  refine ⟨qs, hqs, hne, ?_, ?_⟩
  · intro q hq
    obtain ⟨hprime, hbelow, hminimal⟩ := (hqs q).mp hq
    exact hbound q hprime hbelow hminimal
  · obtain ⟨q, hprime, hbelow, hminimal, hqeq⟩ := hattain
    exact ⟨q, (hqs q).mpr ⟨hprime, hbelow, hminimal⟩, hqeq⟩

end AlgebraicGeometry
