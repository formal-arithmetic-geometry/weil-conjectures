/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Levelwise isomorphisms and specified derived limits

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-r-lim-levelwise-isomorphism, order 1326; Stacks Project,
Derived Categories, Tags 08TC, 0H9J and 014A
(blueprint: lemma-weil-pbc-r-lim-levelwise-isomorphism).

The derived-limit definition selects no functor. The assertion concerns every
completion of the product maps to a morphism of the specified Roos triangles.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- Every Roos-triangle completion of a compatible levelwise isomorphism is invertible.
Source: blueprint order 1326; Stacks Tags 08TC, 0H9J and 014A
(blueprint: lemma-weil-pbc-r-lim-levelwise-isomorphism).

Proof: The compatibility equation says the product map `Limits.Pi.map φ` commutes with the
transition shifts, hence with `1 - shift`. The two displayed equations say that `ψ`,
together with this product map twice, forms a morphism of the specified Roos triangles.
The product map is invertible: its inverse is the product of the inverses of `φ n`,
as checked on every projection. Apply the five lemma for distinguished triangles,
`Pretriangulated.isIso₁_of_isIso₂₃` (lem-weil-derived-limit-levelwise-iso), to conclude
that `ψ` is invertible. Only the two specified products are needed, not all countable
products. The index `n : ℕ` denotes the source's level `n + 1`. No canonical completion
or uniqueness is asserted. -/
theorem isIso_derivedLimit_of_levelwise {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {M N : ℕ → C} [HasProduct M] [HasProduct N]
    (f : ∀ n : ℕ, M (n + 1) ⟶ M n) (g : ∀ n : ℕ, N (n + 1) ⟶ N n)
    (L L' : C) (p : L ⟶ ∏ᶜ M) (p' : L' ⟶ ∏ᶜ N)
    (δ : ∏ᶜ M ⟶ L⟦(1 : ℤ)⟧) (δ' : ∏ᶜ N ⟶ L'⟦(1 : ℤ)⟧)
    (hL : IsDerivedLimitTriangle f L p δ) (hL' : IsDerivedLimitTriangle g L' p' δ')
    (φ : ∀ n : ℕ, M n ⟶ N n)
    (hφ : ∀ n : ℕ, f n ≫ φ n = φ (n + 1) ≫ g n) [∀ n : ℕ, IsIso (φ n)]
    (ψ : L ⟶ L') (hp : ψ ≫ p' = p ≫ Limits.Pi.map φ)
    (hδ : δ ≫ ψ⟦(1 : ℤ)⟧' = Limits.Pi.map φ ≫ δ') : IsIso ψ := by
  sorry

end CategoryTheory
