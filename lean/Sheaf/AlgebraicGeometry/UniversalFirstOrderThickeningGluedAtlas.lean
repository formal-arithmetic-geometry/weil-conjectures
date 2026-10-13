/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# The scheme obtained by gluing local universal thickenings

Source: Stacks Project, More on Morphisms, Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering".
(blueprint: lem-weil-pbc-universal-first-order-thickening-glued-atlas)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Glue the schemes of local universal thickenings. The conclusion provides a
first order thickening and its universal charts; global universality is not asserted.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering", up to "is a universal
first order thickening of Z_i over X".
(blueprint: lem-weil-pbc-universal-first-order-thickening-glued-atlas)

Proof:
1. On each overlap of `C`, restrict the two local thickenings using the first and
   second clauses of `universalFirstOrderThickening_open_pieces` (whole base open).
   They are universal thickenings of the same overlap over `X`.
2. The uniqueness theorem for universal thickenings supplies a unique isomorphism
   between them over `X` and fixing the overlap. On triple intersections both
   composites have these same properties, so uniqueness proves the cocycle equation.
3. Form the scheme glue data of these open overlaps and isomorphisms and take its
   glued scheme `W`. Its open immersions give an open cover `D`. The local maps to
   `X` agree on overlaps and glue to `p`. The maps from the source cover into `W`
   also agree, hence glue to `j : Z ⟶ W`. Check `j ≫ p = h` on `C`.
4. The inverse image under `j` of each glued chart is the corresponding source
   chart. Indeed membership may be checked in a source chart, where the gluing
   equivalence identifies exactly the prescribed open overlap. Thus the pullback
   of `j` to each chart of `D` identifies with its given local immersion.
5. Closed immersion is local on the target. The local defining ideals square to
   zero and are restrictions of the global kernel ideal, so this ideal also squares
   to zero. Therefore `j` is a first order thickening. By the pullback identifications
   in step 4, the universality of each given chart is precisely the final clause. -/
theorem universalFirstOrderThickening_gluedAtlas
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (j : Z ⟶ W) (p : W ⟶ X) (D : W.OpenCover.{u}),
      IsFirstOrderThickening j ∧ j ≫ p = h ∧
        ∀ k, IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
          (D.pullbackHom j k) (D.f k ≫ p) := by sorry

end AlgebraicGeometry
