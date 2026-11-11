/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Eigenvalues along a filtration

If an endomorphism `f` of a finite-dimensional vector space preserves a finite filtration
`0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = V`, its eigenvalues, counted with algebraic multiplicity, are the
union of its eigenvalues on the graded pieces `F (i + 1) ⧸ F i`: the multiset of roots of the
characteristic polynomial of `f` is the sum of the multisets of roots of the characteristic
polynomials of the induced endomorphisms of the graded pieces
(`LinearMap.charpoly_roots_eq_sum_charpoly_roots_mapQ_of_le`). Over an algebraically closed
field these are the eigenvalues with multiplicity; the statement holds over any field.
-/

@[expose] public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Eigenvalues along a filtration.** If `f` preserves a finite filtration
`0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = V`, the multiset of roots of the characteristic polynomial of `f` is
the sum of those of the endomorphisms induced by `f` on the graded pieces `F (i + 1) ⧸ F i`: the
eigenvalues with algebraic multiplicity are the union of those on the graded pieces.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem charpoly_roots_eq_sum_charpoly_roots_mapQ_of_le (f : V →ₗ[K] V)
    (F : ℕ → Submodule K V) (n : ℕ) (h0 : F 0 = ⊥) (hn : F n = ⊤)
    (hle : ∀ i < n, F i ≤ F (i + 1)) (hF : ∀ i, F i ≤ (F i).comap f) :
    f.charpoly.roots = ∑ i ∈ Finset.range n,
      (((F i).comap (F (i + 1)).subtype).mapQ ((F i).comap (F (i + 1)).subtype)
        (f.restrict (hF (i + 1))) fun _ hx ↦ hF i hx).charpoly.roots := by
  rw [charpoly_eq_prod_charpoly_mapQ_of_le f F n h0 hn hle hF,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun _ _ ↦ (charpoly_monic _).ne_zero),
    Finset.sum_eq_multiset_sum, Multiset.bind]
  rfl

end LinearMap
