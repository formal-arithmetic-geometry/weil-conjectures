/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Geometric stalks of closed direct image on algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 0DK1 and 04E5(2); Étale Cohomology,
Tag 04FX (blueprint: lem-sfb-space-closed-pushforward-geometric-stalks).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed direct image has the original abelian geometric stalk on the closed subspace,
and zero stalk on its complement. The natural isomorphism is normalized on every section
germ by the two projections of the scheme fibre product. The quantification over `v`
describes its induced point without choosing a lift: the pullback universal property
supplies exactly one such `v`. Closed immersion is tested on every scheme base change,
using Mathlib's relative morphism property and the existing scheme closed immersion.

Source: Stacks, Tags 0DK1 (correcting the source's swapped point subscripts), 04E5(2)
and 04FX (blueprint: lem-sfb-space-closed-pushforward-geometric-stalks).

Proof:
1. Choose a surjective étale scheme atlas and a point above the given geometric point.
Use lem-sfb-etale-geometric-point-specified-lift to lift over the original algebraically
closed field. Its base change by the closed immersion is a scheme closed immersion;
lem-trf-space-representable-etale-scheme-tests gives the étale projection to the source.
2. On an étale scheme over the chart, direct image is sections over its closed base
change. Fibre-product pasting identifies this with scheme direct image after restriction.
This identity commutes with restrictions and abelian sheaf morphisms.
3. A stalk is unchanged on a fixed pointed étale chart: for any other neighbourhood,
take its fibre product with that chart. It is terminal among chart-neighbourhoods equipped
with a pointed map to the other neighbourhood. Restriction therefore extends cocones
uniquely, giving the two inverse colimit identifications, with the usual germ maps.
4. Apply lemma-openclosed-stalk-lowerstar on the scheme chart. Compose its natural
isomorphism with the preceding stalk identifications. On a section representative the
result is the germ of that same section on its closed base change; chart refinement
shows this is precisely the displayed formula, independent of the atlas.
5. Outside the closed subspace the lifted point is outside the scheme closed subset:
a field point lying in that subset kills its defining ideal and would factor through it.
Its complementary open is étale by lem-weil-pbc-open-immersion-etale. All closed base
changes there are empty. The empty-cover sheaf axiom gives the zero section group, hence
zero stalk, by the chart-colimit identification of Step 3.
6. Both composites for a sheaf morphism send a section to the germ of its image.
Restriction commutes with that morphism and preserves addition and zero. This gives the
natural isomorphism with the claimed germ normalization. -/
theorem closed_pushforward_geometric_stalks
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (hi : (MorphismProperty.inverseImage (@IsClosedImmersion) (Over.forget S)).relative
      yoneda i.hom.hom) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (CommRingCat.of Ω) ⟶ S)
      (z : yoneda.obj (Over.mk b) ⟶ Z.obj.obj),
      ∃ e : representableAbelianDirectImage i hi.rep ⋙
          X.abelianStalk (z ≫ i.hom.hom) ≅ Z.abelianStalk z,
        ∀ (A : Sheaf Z.etaleTopology AddCommGrpCat.{u + 1})
          (N : X.PointedEtale (z ≫ i.hom.hom))
          (v : Over.mk b ⟶
            ((representableEtaleBaseChange i hi.rep).functor.obj N.right).obj.left)
          (hz : yoneda.map v ≫
            ((representableEtaleBaseChange i hi.rep).functor.obj N.right).obj.hom = z),
          v ≫ (representableEtaleBaseChange i hi.rep).projection.app N.right =
            N.hom.left →
          X.abelianGerm (z ≫ i.hom.hom) N
              ((representableAbelianDirectImage i hi.rep).obj A) ≫ e.hom.app A =
            Z.abelianGerm z
              (StructuredArrow.mk (CostructuredArrow.homMk v hz)) A) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (CommRingCat.of Ω) ⟶ S)
      (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      (¬ ∃ z : yoneda.obj (Over.mk b) ⟶ Z.obj.obj, z ≫ i.hom.hom = x) →
      ∀ A : Sheaf Z.etaleTopology AddCommGrpCat.{u + 1},
        IsZero ((X.abelianStalk x).obj
          ((representableAbelianDirectImage i hi.rep).obj A))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
