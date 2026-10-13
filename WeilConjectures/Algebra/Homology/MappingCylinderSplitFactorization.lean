/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Mapping-cylinder split factorization of a cochain map

Source: Stacks Project, Derived Categories, Lemma 013N, Definition 014G, and Remark 013O
(blueprint: lem-weil-pbc-complex-mapping-cylinder-split-factorization).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- A cochain map in an additive category factors through a termwise direct-summand inclusion
and a deformation retraction, preserving the specified upper bound and lowering the specified
lower bound by one. Source: Stacks Project, Lemma 013N, Definition 014G, and Remark 013O
(blueprint: lem-weil-pbc-complex-mapping-cylinder-split-factorization).

Proof (the six steps of the node):
1. Using finite biproducts (`def-weil-additive-category`), take
   `Tⁿ = Lⁿ ⊕ Kⁿ ⊕ Kⁿ⁺¹`, with differential matrix having rows
   `(d_L, 0, 0)`, `(0, d_K, id)`, and `(0, 0, -d_K)`.
   Matrix composition uses bilinearity (`def-weil-preadditive-category`).
2. Squaring this matrix gives zero: the diagonal entries are squares of differentials and
   the only additional entry is `d_K - d_K`.
3. Set `i = (α, id, 0)`, `p = (id, 0, 0)`, and `s = (id, 0, 0)` as a column.
   These commute with the differentials; their components give `i ≫ p = α` and `s ≫ p = id`.
4. In degree `n`, put `M = Lⁿ ⊕ Kⁿ⁺¹`. The isomorphism from `Kⁿ ⊕ M` to `Tⁿ` is
   `(k,l,k⁺) ↦ (α k + l,k,k⁺)`, with inverse `(l,k,k⁺) ↦ (k,l - α k,k⁺)`.
   Its first column is `i`, so the inverse carries `i` to the first biproduct inclusion.
5. The degree-minus-one map `(l,k,k⁺) ↦ (0,0,k)` gives `id - p ≫ s = dh + hd`.
   Negating it gives the homotopy from `p ≫ s` to `id` used below.
6. A finite biproduct of zero objects is zero. If the terms of `K` and `L` vanish below `n₀`,
   all three summands vanish below `n₀ - 1`; if they vanish above `n₁`, all three vanish above
   `n₁`. The same complex therefore preserves both bounds simultaneously. -/
theorem exists_mapping_cylinder_split_factorization
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {K L : CochainComplex C ℤ} (α : K ⟶ L) :
    ∃ (T : CochainComplex C ℤ) (i : K ⟶ T) (p : T ⟶ L) (s : L ⟶ T),
      i ≫ p = α ∧
      (∀ n : ℤ, ∃ (M : C) (e : T.X n ≅ K.X n ⊞ M), i.f n ≫ e.hom = biprod.inl) ∧
      s ≫ p = 𝟙 L ∧
      Nonempty (Homotopy (p ≫ s) (𝟙 T)) ∧
      (∀ n₀ : ℤ, (∀ n : ℤ, n < n₀ → IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n : ℤ, n < n₀ - 1 → IsZero (T.X n)) ∧
      (∀ n₁ : ℤ, (∀ n : ℤ, n₁ < n → IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n : ℤ, n₁ < n → IsZero (T.X n)) := by
  sorry

end CochainComplex
