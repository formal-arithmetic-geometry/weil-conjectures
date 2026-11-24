/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.RingTheory.BertiniNoether

/-! # Specializing an absolutely irreducible polynomial

We show that an absolutely irreducible polynomial over a domain stays irreducible under every
specialization to a field that does not kill a suitable nonzero element.

## Implementation details

The statement is reduced to `bertini_noether` by passing from the domain `A` to its fraction
field, embedded into the algebraic closure of the field `K`.

## References

* Stacks Project, Tag 0557.
-/

@[expose] public section

universe u
namespace MvPolynomial

/-- Let `A` be a domain contained in a field `K` and `P` a polynomial over `A` which is
irreducible over an algebraic closure of `K`. Then there is a nonzero `a ∈ A` such that for every
ring map `φ : A → L` to a field with `φ a ≠ 0`, the polynomial `map φ P` is irreducible. -/
theorem exists_nonzero_irreducible_specializations
    {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    (n : ℕ) (P : MvPolynomial (Fin n) A) (ι : A →+* K)
    (hι : Function.Injective ι)
    (hP : Irreducible (map ((algebraMap K (AlgebraicClosure K)).comp ι) P)) :
    ∃ a : A, a ≠ 0 ∧ ∀ (L : Type u) [Field L] (φ : A →+* L),
      φ a ≠ 0 → Irreducible (map φ P) := by
  let j : A →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp ι
  have hj : Function.Injective j := (algebraMap K (AlgebraicClosure K)).injective.comp hι
  let f : FractionRing A →+* AlgebraicClosure K := IsFractionRing.lift hj
  let : Algebra (FractionRing A) (AlgebraicClosure K) := f.toAlgebra
  have hf : (algebraMap (FractionRing A) (AlgebraicClosure K)).comp
      (algebraMap A (FractionRing A)) = j := by
    ext x
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) hj x
  have hP' : Irreducible (map ((algebraMap (FractionRing A) (AlgebraicClosure K)).comp
      (algebraMap A (FractionRing A))) P) := by
    rw [hf]
    exact hP
  obtain ⟨a, ha, hs⟩ := bertini_noether P (FractionRing A) (AlgebraicClosure K) hP'
  exact ⟨a, ha, fun L _ φ hφ ↦ (hs φ hφ).1⟩

end MvPolynomial
