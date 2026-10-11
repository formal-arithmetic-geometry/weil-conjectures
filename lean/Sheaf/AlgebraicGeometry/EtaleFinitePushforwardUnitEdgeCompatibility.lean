/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Compatibility of base-changed edge maps with the pushforward of a unit

Source: Stacks Project, Etale Cohomology, Lemma 09ZE
(`lemma-efface-cohomology-on-closed-by-finite-cover`), proof, second paragraph
(blueprint: lem-weil-pbc-finite-pushforward-unit-edge-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Base-changed exchange followed by the edge map carries the pushforward of the unit
for `π` to pullback along `πZ`, followed by the canonical composition comparison.
Source: Stacks Project, Lemma 09ZE (`lemma-efface-cohomology-on-closed-by-finite-cover`),
proof, second paragraph; the compatibility used there is formulated by the node's agent
(blueprint: lem-weil-pbc-finite-pushforward-unit-edge-compatibility).

Proof (the eight steps of the node):
1. Set `A = f_* G`, `B = i^* A`, and `A' = (π ≫ f)_* π^* G`. The two cartesian
squares and the equations for `πZ` identify every composite to `X`. Use the units,
counits and composition isomorphisms of def-weil-pbc-inverse-image,
def-weil-pbc-direct-image and lem-weil-pbc-inverse-image-composition. Exchange is the
adjoint of the square comparison followed by inverse image of the counit. Fix
resolutions and use lem-weil-pbc-cohomology-pullback-functorial to identify all choices.
2. By lem-weil-pbc-adjunct-counit-identity and naturality of cohomological pullback,
exchange followed by the edge map is pullback followed by cohomology of its adjunct.
3. Naturality and composition of cohomological pullback reduce the required equality
to the equality of sheaf morphisms from `(fZ')^* B` to `(iY')^* π^* G`.
4. The counit for `π ≫ f` composed with inverse image of `f_* η_π` is inverse image
of the counit for `f`, after the composition comparison. This follows from the unit
formula of lem-weil-pbc-inverse-image-composition, naturality of the unit, and the
triangle identity of lem-weil-pbc-adjunct-counit-identity.
5. Expand the adjunct for the second square and move the unit morphism through the
composition isomorphisms by naturality; apply step 4.
6. Expand the adjunct for the first square and move its counit through the comparison
κ by naturality of the composition isomorphisms.
7. The remaining comparisons agree by associativity of the composition isomorphisms
(lem-weil-pbc-derived-inverse-image-composition), applied to `(f, π, iY')`,
`(f, iY, πZ)` and `(i, fZ, πZ)` in the node's order of composition.
8. Substitute this comparison identity in steps 5 and 6, then apply step 3.
No finiteness hypothesis is used; the identity base change is included. -/
theorem cohomology_baseChange_unit_edge_compatibility
    {X Y Y' Z YZ YZ' : Scheme.{u}} (f : Y ⟶ X) (π : Y' ⟶ Y) (i : Z ⟶ X)
    (iY : YZ ⟶ Y) (fZ : YZ ⟶ Z) (iY' : YZ' ⟶ Y') (fZ' : YZ' ⟶ Z)
    (πZ : YZ' ⟶ YZ) (sq : IsPullback iY fZ f i)
    (sq' : IsPullback iY' fZ' (π ≫ f) i)
    (sqπ : CommSq iY' πZ π iY) (hZ : πZ ≫ fZ = fZ')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ').counit.app
        ((upperStar AddCommGrpCat.{u + 1} iY').obj
          ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q).comp
      ((cohomologyMap fZ' ((lowerStar AddCommGrpCat.{u + 1} fZ').obj
        ((upperStar AddCommGrpCat.{u + 1} iY').obj
          ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q).comp
        ((Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq'.toCommSq).app
          ((upperStar AddCommGrpCat.{u + 1} π).obj G)) q).comp
          (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} i).map
            ((lowerStar AddCommGrpCat.{u + 1} f).map
                ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).unit.app G) ≫
              (lowerStarComp AddCommGrpCat.{u + 1} π f).hom.app
                ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q))) =
      (Sheaf.H.map ((squareUpperStarIso AddCommGrpCat.{u + 1} sqπ).hom.app G) q).comp
        ((cohomologyMap πZ ((upperStar AddCommGrpCat.{u + 1} iY).obj G) q).comp
          ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ).counit.app
            ((upperStar AddCommGrpCat.{u + 1} iY).obj G)) q).comp
            ((cohomologyMap fZ ((lowerStar AddCommGrpCat.{u + 1} fZ).obj
              ((upperStar AddCommGrpCat.{u + 1} iY).obj G)) q).comp
              (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app G) q)))) := by
  sorry

end AlgebraicGeometry.Etale
