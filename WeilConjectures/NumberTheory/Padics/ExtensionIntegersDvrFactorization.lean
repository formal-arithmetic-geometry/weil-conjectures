/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Uniformizer factorizations in a DVR

We show that generators of the maximal ideal of a DVR are associated, and that every nonzero
element of the fraction field is a unit times an integer power of a fixed generator.

## Implementation details

The standard DVR API expresses every nonzero element as a unit times a power of an
irreducible generator, and its fraction-field version gives the integer-power expression.

## References

* Stacks Project, Algebra, Definition 00IE and Lemma 00PD.
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace Padic

/-- In a domain DVR, generators of a fixed nonzero maximal ideal are associated and every
nonzero fraction has a unit-times-integer-power expression. -/
theorem extension_integers_dvr_factorization (E : Type*) [Field E] (O : Subring E)
    (m : Ideal O) (hDVR : IsDiscreteValuationRing O) (_hm0 : m ≠ ⊥)
    (hmax : m.IsMaximal) (hfrac : IsFractionRing O E)
    (_hgen : ∃ π : O, Ideal.span ({π} : Set O) = m) :
    (∀ π π' : O, Ideal.span ({π} : Set O) = m →
      Ideal.span ({π'} : Set O) = m → ∃ v : Oˣ, π' = (v : O) * π) ∧
    (∀ π : O, Ideal.span ({π} : Set O) = m → ∀ x : Eˣ,
      ∃ p : Oˣ × ℤ, (x : E) = ((p.1 : O) : E) * (π : E) ^ p.2) := by
  letI : IsDiscreteValuationRing O := hDVR
  letI : IsFractionRing O E := hfrac
  have hm_eq : m = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hirr_of_gen : ∀ {π : O}, Ideal.span ({π} : Set O) = m → Irreducible π := by
    intro π hπ
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
    rw [← hm_eq, hπ]
  constructor
  · intro π π' hπ hπ'
    have hπi := hirr_of_gen hπ
    have hπ'i := hirr_of_gen hπ'
    obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible O hπi hπ'i
    refine ⟨u, ?_⟩
    exact hu.symm.trans (mul_comm _ _)
  · intro π hπ x
    have hπi := hirr_of_gen hπ
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπi x.ne_zero
    refine ⟨⟨u, n⟩, ?_⟩
    change (x : E) = (algebraMap O E (u : O)) * (algebraMap O E π) ^ n
    exact hu

end Padic
