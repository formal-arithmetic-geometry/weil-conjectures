/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finite affine refinements of algebraic-space scheme tests

Source: Stacks Project, Spaces Descent, Tag 041L; Topologies, Tags 022B and 022D;
Properties of Spaces, Tag 03H4
(blueprint: lem-sfb-space-fpqc-finite-affine-test-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine test of a space over an fpqc-covered scheme has a finite covering on
points by spaces that are affine tests of the local base changes. No quasi-compactness
hypothesis on `f` or its base changes is required, and none of these test spaces is
asserted to be quasi-compact.
Source: Stacks Project, Spaces Descent, Tag 041L, affine-test argument; Topologies,
Tags 022B and 022D; Properties of Spaces, Tag 03H4
(blueprint: lem-sfb-space-fpqc-finite-affine-test-cover).

Proof: form `A = X ×_T Z` and `Z_i = Z ×_T T_i` using algebraic-space and scheme
fibre products. By fpqc base-change stability (Tag 022D), the projections `Z_i → Z`
form an fpqc covering. Since `Z` is affine, its finite affine refinement (Tag 022B)
gives finitely many affine opens `W_j` in members `Z_i` with images covering `Z`.
Let `w_j : W_j → T_i` be the composite with the second scheme projection and put
`B_j = (X ×_T T_i) ×_{T_i} W_j`. The fibre-product projections give the stated
representing squares. Associativity identifies `B_j` with `A ×_Z W_j`, and yields
`r_j : B_j → A`. Given a point of `A`, choose a point of some `W_j` over its image
in `Z`; the compatible-point lifting property (Tag 03H4) supplies a point of
`A ×_Z W_j` above it. Transport this point to `B_j`. If there are no refinement
members, `Z` has no points and neither does `A`, so the empty finite covering works.
The construction does not compose a flat map with an atlas and call it etale. -/
theorem fpqc_finite_affine_test_cover
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) {I : Type v}
    (Tᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hg : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left)
    (Z : Over S) (hZ : IsAffine Z.left) (h : yoneda.obj Z ⟶ yoneda.obj T) :
    ∃ (A : AlgebraicSpace S) (q : A.obj.obj ⟶ X.obj.obj)
      (p : A.obj.obj ⟶ yoneda.obj Z), IsPullback q p f h ∧
        ∃ (n : ℕ) (i : Fin n → I) (W : Fin n → Over S)
          (w : ∀ j, W j ⟶ Tᵢ (i j)) (B : Fin n → AlgebraicSpace S)
          (b : ∀ j, (B j).obj.obj ⟶ Limits.pullback f (yoneda.map (g (i j))))
          (c : ∀ j, (B j).obj.obj ⟶ yoneda.obj (W j)) (r : ∀ j, B j ⟶ A),
          (∀ j, IsAffine (W j).left) ∧
            (∀ j, IsPullback (b j) (c j) (pullback.snd f (yoneda.map (g (i j))))
              (yoneda.map (w j))) ∧
            ∀ x : Point A.obj.obj, ∃ (j : Fin n) (y : Point (B j).obj.obj),
              mapPoint (r j).hom.hom y = x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
