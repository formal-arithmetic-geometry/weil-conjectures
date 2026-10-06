/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The geometric Frobenius of an algebraic extension of a finite field

Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic K L` is the *arithmetic* Frobenius
`σ : x ↦ x ^ #K` of an algebraic extension `L` of a finite field `K`, viewed as an element of
the group `Gal(L/K) = L ≃ₐ[K] L`. The *geometric* Frobenius is its inverse, and it is the
automorphism that acts on étale cohomology in the Weil conjectures.

## Main definitions

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`: the geometric Frobenius `σ⁻¹`.

## Main statements

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv`: the geometric Frobenius is the
  inverse of the arithmetic Frobenius. Both `σ⁻¹ * σ = 1` and `σ * σ⁻¹ = 1` follow by `simp`.
- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq`: the `m`-th power
  of the geometric Frobenius fixes the image of a field with `#K ^ m` elements.
- `FiniteField.frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff`: the fixed field of the arithmetic
  Frobenius is `K`.
-/

@[expose] public section

namespace FiniteField

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Blueprint `sk-d-ab-field`: Finite fields, Frobenius and abelian varieties.

Fix a finite field `K` with `q` elements and an algebraic extension `L`. The *arithmetic
Frobenius* is `σ : x ↦ x ^ q`; the *geometric Frobenius* is `F = σ⁻¹`. -/
@[simps!]
noncomputable def geometricFrobeniusAlgEquivOfAlgebraic : Gal(L/K) :=
  (frobeniusAlgEquivOfAlgebraic K L)⁻¹

@[simp]
theorem geometricFrobeniusAlgEquivOfAlgebraic_eq_inv :
    geometricFrobeniusAlgEquivOfAlgebraic K L = (frobeniusAlgEquivOfAlgebraic K L)⁻¹ :=
  rfl

/-- The `m`-th power of the geometric Frobenius of `L/K` fixes the image of any embedding of a
field `E` with `#K ^ m` elements: such a field is fixed pointwise by `x ↦ x ^ (#K ^ m)`. -/
theorem geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq {E : Type*} [Field E]
    [Finite E] (m : ℕ) (hE : Nat.card E = Fintype.card K ^ m) (ι : E →+* L) (a : E) :
    (geometricFrobeniusAlgEquivOfAlgebraic K L ^ m) (ι a) = ι a := by
  have := Fintype.ofFinite E
  rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  rw [← map_pow, ← hE, Nat.card_eq_fintype_card, pow_card]

/-- The elements of `L` fixed by the arithmetic Frobenius `x ↦ x ^ q` are exactly the elements
of `K`: every element of `K` is a root of `X ^ q - X`, and this polynomial has at most `q` roots
in `L`. -/
theorem frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff {x : L} :
    frobeniusAlgEquivOfAlgebraic K L x = x ↔ x ∈ Set.range (algebraMap K L) := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ AlgEquiv.commutes _ a⟩
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set f : Polynomial L := Polynomial.X ^ Fintype.card K - Polynomial.X
  have hf : f ≠ 0 := X_pow_card_sub_X_ne_zero L hq
  have hroot {y : L} : y ∈ f.roots.toFinset ↔ y ^ Fintype.card K = y := by
    simp [f, Polynomial.mem_roots hf, sub_eq_zero]
  have himage : Finset.univ.image (algebraMap K L) = f.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [hroot, ← map_pow, pow_card]
    · rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ]
      calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hx' : x ∈ f.roots.toFinset := hroot.mpr hx
  rw [← himage] at hx'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx'
  exact ⟨a, rfl⟩

end FiniteField
