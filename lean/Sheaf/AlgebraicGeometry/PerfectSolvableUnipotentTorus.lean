module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # The unipotent part of a perfect-field solvable algebraic group

Source: Milne, Algebraic Groups, Theorem 16.33(a)--(c), pp.335--336,
and Proposition 1.90, p.33 (blueprint: lem-sfb-perfect-solvable-unipotent-torus).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open SolvableGroupStructure

/-- A smooth connected solvable group over a perfect field has a smooth connected
normal unipotent part and torus quotient, compatible with arbitrary field extension
and invariant under all automorphisms after every field extension. It is normal
in a smooth ambient group whenever the original group is normal there.
Source: Milne, Theorem 16.33(a)--(c) and Proposition 1.90
(blueprint: lem-sfb-perfect-solvable-unipotent-torus).

Proof:
1. Over the algebraic closure apply Lie--Kolchin
(`lem-sfb-lie-kolchin-triangular-embedding`) and intersect with the upper
unitriangular group. The diagonal-kernel lemma
(`lem-sfb-triangular-diagonal-kernel`) makes the kernel smooth, connected,
normal and unipotent; the quotient is a smooth connected subgroup of a split
torus, hence a torus (`lem-sfb-multiplicative-type-largest-subtorus`).
Scalar-extension properties are `lem-sfb-solvable-normal-subgroup-products`.
2. Every unipotent subgroup maps trivially to a multiplicative-type quotient
(`lem-sfb-unipotent-to-multiplicative-trivial`). The scheme-theoretic kernel
property (`lem-sfb-affine-normal-quotient-geometry`) gives containment, and
applying containment twice gives uniqueness of this kernel.
3. Perfectness makes the algebraic closure Galois. Each Galois transform has
the same properties, so uniqueness makes its defining ideal Galois-stable.
Descend the subgroup and normality by `lem-sfb-galois-descent-affine-subgroups`;
smoothness descends by `lem-trf-smooth-fpqc-base-descent`. A disconnection
would pull back to a disconnection upstairs. Unipotence is detected after
extension, and the represented quotient commutes with base change
(`lem-sfb-affine-normal-quotient-geometry`), hence becomes a split torus.
4. After ANY field extension, including imperfect transcendental extensions,
the same kernel remains smooth, connected, normal and unipotent, and its
quotient is the base-changed torus. Repeat step 2 to get maximality over the
extension. This is formation compatibility, without perfectness of that field.
5. An automorphism after field extension carries this kernel to another with
the same properties. Uniqueness, or maximality applied to it and its inverse,
gives an automorphism of the subgroup commuting with its inclusion.
6. If the original group is normal in a smooth ambient group, geometric
conjugation preserves it and step 5 preserves its unipotent part. Apply
`lem-sfb-smooth-ambient-normality-geometric` to deduce ambient normality. -/
theorem perfect_solvable_unipotent_torus {k : Type u} [Field k] [PerfectField k]
    (H : Grp (Over (Spec (.of k)))) (hH : IsAlgebraic H)
    (hsm : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) (hs : IsSolvable H) :
    ∃ (U : Grp (Over (Spec (.of k)))) (i : U ⟶ H)
      (Q : Grp (Over (Spec (.of k)))) (q : H ⟶ Q),
      IsAlgebraic U ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      IsAlgebraic Q ∧ IsTorus Q ∧ IsFppfQuotient i.hom.hom q ∧
      (∀ (W : Grp (Over (Spec (.of k)))) (j : W ⟶ H),
        IsAlgebraic W → IsUnipotent W → IsClosedSubgroupScheme j.hom.hom →
          ∃ l : W ⟶ U, l ≫ i = j) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        IsUnipotent ((extend K).obj U) ∧
        ConnectedSpace ((extend K).obj U).X.left ∧
        IsClosedSubgroupScheme ((extend K).map i).hom.hom ∧
        IsNormalSubgroupScheme ((extend K).map i).hom.hom ∧
        IsTorus ((extend K).obj Q) ∧
        IsFppfQuotient ((extend K).map i).hom.hom ((extend K).map q) ∧
        (∀ (W : Grp (Over (Spec (.of K)))) (j : W ⟶ (extend K).obj H),
          IsAlgebraic W → IsUnipotent W → IsClosedSubgroupScheme j.hom.hom →
            ∃ l : W ⟶ (extend K).obj U, l ≫ (extend K).map i = j) ∧
        (∀ a : (extend K).obj H ≅ (extend K).obj H,
          ∃ b : (extend K).obj U ≅ (extend K).obj U,
            b.hom ≫ (extend K).map i = (extend K).map i ≫ a.hom)) ∧
      (∀ (G : Grp (Over (Spec (.of k)))) (j : H ⟶ G),
        IsAlgebraic G → Smooth G.X.hom → IsClosedSubgroupScheme j.hom.hom →
          IsNormalSubgroupScheme j.hom.hom → IsNormalSubgroupScheme (i ≫ j).hom.hom) := by
  sorry

end AlgebraicGeometry
