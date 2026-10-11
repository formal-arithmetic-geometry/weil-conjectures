/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker F1
-/
module

public import Sheaf.Algebra.Homology.ZigzagModule

/-!
# Functoriality of zig-zag modules

Source: Stacks Project, Algebra, Tag 00M1, proof and preceding functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-zigzag-module-functorial).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

/-- (blueprint: lem-weil-pbc-double-complex-zigzag-module-functorial)
Trivial zig-zags are zig-zags, and the quotient maps are functorial
(Stacks Project, Algebra, Tag 00M1, proof and preceding paragraph).

Proof, following the four steps of the node:
(a) For `a = D b`, apply `d` and `δ` to the two adjacent components. The `dd` and
`δδ` terms vanish; the remaining terms agree by the commuting square. Thus `B ≤ Z`,
and the intersection with `Z` is `B`.
(b) Apply the component maps of `Φ` to the zig-zag equalities. Since they commute
with both differentials, the resulting tuple is a zig-zag. Linearity and the same
commutation identities give `Φ (D b) = D (Φ b)` componentwise, so boundaries map to
boundaries. These steps use the double-complex and zig-zag definitions.
(c) Restrict `Φ` to cycles and apply the quotient-induced-map lemma
`lem-weil-pbc-quotient-module-induced-map` (`Submodule.mapQ`, `mapQ_mkQ`, and
`linearMap_qext`). This gives the displayed representative formula and uniqueness.
(d) Composition and identity are componentwise on cycles. Apply the same lemma's
composition and identity clauses (`Submodule.mapQ_comp` and `mapQ_id`).

In the representative formula, `b` is a cycle whose underlying tuple is `Φ(a)`;
this avoids choosing a second restriction map or a second quotient definition. -/
theorem zigzagModule_functorial
    {R : Type u} [CommRing R]
    (A B C : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℕ) :
    zigzagBoundaries A n ≤ zigzagCycles A n ∧
    zigzagCycles A n ⊓ zigzagBoundaries A n = zigzagBoundaries A n ∧
    (zigzagCycles A n).map (zigzagTotalMap Φ n) ≤ zigzagCycles B n ∧
    (zigzagTotalMap Φ n).comp (zigzagBoundary A n) =
      (zigzagBoundary B n).comp (zigzagTotalMap Φ (n + 1)) ∧
    (zigzagBoundaries A n).map (zigzagTotalMap Φ n) ≤ zigzagBoundaries B n ∧
    (∀ (a : zigzagCycles A n) (b : zigzagCycles B n),
      b.val = zigzagTotalMap Φ n a.val →
      zigzagMap Φ n (Submodule.Quotient.mk a) = Submodule.Quotient.mk b) ∧
    (∀ f : zigzagModule A n →ₗ[R] zigzagModule B n,
      (∀ (a : zigzagCycles A n) (b : zigzagCycles B n),
        b.val = zigzagTotalMap Φ n a.val →
        f (Submodule.Quotient.mk a) = Submodule.Quotient.mk b) → f = zigzagMap Φ n) ∧
    zigzagMap (Φ ≫ Ψ) n = (zigzagMap Ψ n).comp (zigzagMap Φ n) ∧
    zigzagMap (𝟙 A) n = LinearMap.id := by
  sorry

end HomologicalComplex₂
