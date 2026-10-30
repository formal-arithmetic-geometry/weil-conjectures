/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis

/-!
# Frobenius-closed bases of function fields inside a bigger field

Let `ℓ` be a field of characteristic `p`, `k ≤ E` subfields of `ℓ` with `k` algebraically closed,
and `x ∈ E` transcendental over `k` such that `E` is a finite separable extension of `k⟮x⟯`.
Then `E` has a Frobenius-closed `k`-basis `1, w i ^ p ^ n`
(`FrobeniusClosedBasis.exists_frobeniusClosed_basis`), and `x` is a polynomial of degree `< p`
with coefficients in `E ^ p` in any element `ρ ∈ E` which is not a `p`-th power in `E`: indeed
`E = E ^ p (x)` has degree `p` over `E ^ p`, so `E = E ^ p (ρ)`.
-/

@[expose] public section

universe u

namespace FrobeniusClosedBasis

/-- **Frobenius-closed bases of a function field inside a bigger field.** -/
theorem exists_of_subfield {ℓ : Type u} [Field ℓ] (p : ℕ) [Fact p.Prime] [CharP ℓ p]
    (k E : Subfield ℓ) (hkE : k ≤ E) [IsAlgClosed k] {x : ℓ} (hxE : x ∈ E)
    (hx : Transcendental k x)
    (hfin : ∃ N : ℕ, ∀ (n : ℕ) (e : Fin n → ℓ), (∀ i, e i ∈ E) →
      LinearIndependent (IntermediateField.adjoin k {x}) e → n ≤ N)
    (hsep : ∀ e ∈ E, IsSeparable (IntermediateField.adjoin k {x}) e) :
    ∃ (ι : Type u) (w : ι → ℓ), (∀ i, w i ∈ E) ∧
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2) ∧
      (∀ e ∈ E, e ∈ Submodule.span k
        (Set.range fun j : Option (ι × ℕ) ↦ j.elim 1 fun i ↦ w i.1 ^ p ^ i.2)) ∧
      ∀ ρ ∈ E, (∀ z ∈ E, z ^ p ≠ ρ) →
        ∃ y : ℕ → ℓ, (∀ j, y j ∈ E) ∧ x = ∑ j ∈ Finset.range p, y j ^ p * ρ ^ j := by
  sorry

end FrobeniusClosedBasis
