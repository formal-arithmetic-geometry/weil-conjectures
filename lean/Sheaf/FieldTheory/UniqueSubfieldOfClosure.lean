/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The unique finite subfield of an algebraic closure

Source: Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`, order 411
(blueprint: lem-weil-unique-subfield-of-closure).
-/

@[expose] public section

universe u v

namespace FiniteField

/-- The roots of `X ^ (q ^ n) - X` in an algebraic closure of a field with `q` elements
form its unique subfield with `q ^ n` elements. The image of the base field is the
root subfield for `n = 1`, is the unique subfield with `q` elements, and lies in every
such subfield. The final ring homomorphism is the corestriction of the base-field map;
via `RingHom.toAlgebra` it supplies the claimed base-field algebra structure.

Source: blueprint `def-weil-finite-field-fiber.md`, order 411
(blueprint: lem-weil-unique-subfield-of-closure).

Proof plan (Lang, Algebra, Ch. V, §5, Theorem 5.1, wanted but not obtained;
the six-step argument is recorded in the DAG):
1. The base field has characteristic `p`; its injective structure map gives the
   closure characteristic `p` too. Put `Q = q ^ n = p ^ (a * n)`; then `p ∣ Q` and `2 ≤ Q`.
2. The arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic` and its `n`-th
   iterate fix precisely the roots of `X ^ Q - X`. Fixed points of a field automorphism
   form a subfield, containing the image of the base field.
3. Over the algebraically closed field, `Polynomial.Splits.eq_prod_roots` factors this
   monic degree-`Q` polynomial into linear factors. By `galois_poly_separable` its roots
   are simple, so there are exactly `Q` distinct roots.
4. For any subfield with `Q` elements, `FiniteField.pow_card` gives `x ^ Q = x`.
   It is therefore contained in the root subfield, and equal to it by finite cardinality.
5. The base-field image has `q` elements by injectivity. Apply uniqueness with `n = 1`
   to identify it with the roots of `X ^ q - X`. Such roots are also roots for every `n`
   by iterating the equation `x ^ q = x`.
6. Corestrict the structure map to the root subfield. Its composite with the inclusion
   is the original structure map, giving the asserted base-field algebra structure. -/
theorem exists_unique_subfield_of_closure
    (p a q : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hq : q = p ^ a)
    (k₀ : Type u) [Field k₀] [Finite k₀] (hcard : Nat.card k₀ = q)
    (k : Type v) [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Subfield k,
      (∀ x : k, x ∈ E ↔ x ^ (q ^ n) = x) ∧
      Nat.card E = q ^ n ∧
      (∀ S : Subfield k, Nat.card S = q ^ n → S = E) ∧
      (algebraMap k₀ k).fieldRange ≤ E ∧
      (∀ x : k, x ∈ (algebraMap k₀ k).fieldRange ↔ x ^ q = x) ∧
      (∀ S : Subfield k, Nat.card S = q → S = (algebraMap k₀ k).fieldRange) ∧
      ∃ ι : k₀ →+* E, E.subtype.comp ι = algebraMap k₀ k := by
  sorry

end FiniteField
