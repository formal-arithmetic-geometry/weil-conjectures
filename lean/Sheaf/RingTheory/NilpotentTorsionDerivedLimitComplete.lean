/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.RingTheory.DerivedCompleteProductsTriangles
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Derived completeness of limits of nilpotent torsion complexes

Source: Stacks Project, More on Algebra, Tag 091W, `lemma-naive-derived-completion`,
with tensor factor `A[0]`
(blueprint: lem-weil-pbc-nilpotent-torsion-derived-limit-complete).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A derived limit of a tower on which each element of `I` acts nilpotently at each
level is derived `I`-complete. The exponent may depend on the element and the level.
Source: Stacks Project, Tag 091W, `lemma-naive-derived-completion`, with tensor factor
`A[0]` (blueprint: lem-weil-pbc-nilpotent-torsion-derived-limit-complete).

Proof:
1. Products of modules are exact: kernels are coordinatewise, and tuples lift across
products of surjections by choice. Apply `lem-weil-derived-limit-existence` to obtain
countable products and derived limits in `D(A)`, unique up to isomorphism.
2. Fix a level and `a ∈ I`, and choose `e ≥ 1` annihilating that level. On the product
of the constant tower, its shift `s` satisfies `pr_j s^r = a^r pr_{j+r}`, by induction
and the product universal property `def-weil-category-product`. Hence `s^e = 0`, and
`1 + s + ... + s^(e-1)` inverts `1 - s` in `def-weil-derived-limit`'s Roos triangle.
3. In that triangle the first and last maps vanish since the middle map is invertible.
Rotate backwards using `def-weil-triangulated-category`. Exactness of Hom into this
triangle (`lem-weil-pbc-hom-into-triangle-exact`) factors the identity of the derived
limit through a zero map, so the derived limit is zero. Thus each level is derived
complete by `def-weil-point-derived-complete-module-complex`.
4. By clause (1) of `lem-weil-pbc-module-derived-complete-products-triangles`, the
product of all levels is derived complete. The Roos triangle for the given tower has
this product as both remaining vertices. Clause (2) of that closure lemma makes its
first vertex derived complete. No uniform exponent over levels is required. -/
theorem isDerivedComplete_of_isDerivedLimit_of_nilpotent
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (I : Ideal A) (L : ℕ → DerivedCategory (ModuleCat.{v} A)) [HasProduct L]
    (t : ∀ n : ℕ, L (n + 1) ⟶ L n)
    (h : ∀ (a : A), a ∈ I → ∀ n : ℕ, ∃ e : ℕ, 1 ≤ e ∧ (a ^ e) • 𝟙 (L n) = 0)
    (H : DerivedCategory (ModuleCat.{v} A)) (hH : IsDerivedLimit t H) :
    IsDerivedComplete I H := by
  sorry

end DerivedCategory
