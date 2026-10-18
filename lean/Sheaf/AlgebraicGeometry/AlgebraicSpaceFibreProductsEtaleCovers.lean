/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Fibre products of algebraic spaces and pullback of étale coverings

Source: Stacks Project, Spaces, Tags 02X2 and 04T9; Topologies on Algebraic Spaces,
Tag 041F(3); Properties of Spaces, Tags 03BU and 03H4
(blueprint: lem-trf-space-fibre-products-etale-covers).

The chosen sheaf pullback is an algebraic space. Its universal property is written with
algebraic-space test objects; morphisms are the same sheaf maps in the full subcategory.

## Main statements

* `fibreProduct_isAlgebraicSpace`: closure and the universal property.
* `etaleCover_pullback`: stability of jointly surjective étale families.
* `etale_fibreProduct_isScheme`: the scheme special case.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sheaf fibre product is an algebraic space and has the categorical universal
property for algebraic-space test objects.
Source: Stacks, Spaces, Tags 04T9 and 02X2
(blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: (1) pairs of matching sections glue uniquely in the two sheaves, giving the sheaf
pullback. (2) On a test scheme, the diagonal is represented by the fibre product of the two
scheme equality loci for the diagonals of `F` and `G`. (3) Choose scheme atlases `U → F`
and `V → G`; `U ×_H V` is a scheme by representability of the diagonal of `H`.
(4) Over a scheme `T → F ×_H G`, this atlas is the fibre product over `T` of the two
surjective étale scheme atlas pullbacks. Scheme surjectivity and étaleness are stable under
base change and composition, so it is a surjective étale atlas.
The scheme permanence inputs are [lem-weil-pbc-surjective-base-change],
[lem-weil-pbc-etale-scheme-base-change], [lem-trf-surjective-morphism-composition], and
[lem-weil-pbc-etale-composition-cancellation]; the sheaf condition uses
[def-weil-pbc-sites-and-cohomology] and [def-trf-algebraic-space].
(5) A map from any algebraic space `Q` into the pullback is uniquely the compatible pair
of maps into `F` and `G`, since algebraic spaces form a full subcategory of sheaves. -/
theorem fibreProduct_isAlgebraicSpace {S : Scheme.{u}} (F G H : AlgebraicSpace S)
    (f : F ⟶ H) (g : G ⟶ H) :
    IsAlgebraicSpace (Limits.pullback f.hom g.hom) ∧
      ∀ (Q : AlgebraicSpace S) (a : Q ⟶ F) (b : Q ⟶ G), a ≫ f = b ≫ g →
        ∃! l : Q.obj ⟶ Limits.pullback f.hom g.hom,
          l ≫ Limits.pullback.fst f.hom g.hom = a.hom ∧
          l ≫ Limits.pullback.snd f.hom g.hom = b.hom := by
  sorry

/-- Pulling back a jointly surjective representable étale family preserves both properties.
The fibre products are algebraic spaces by `fibreProduct_isAlgebraicSpace`.
Source: Stacks, Topologies on Algebraic Spaces, Tag 041F(3); Properties of Spaces,
Tags 03BU and 03H4 (blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: (6) For each test scheme `T → G`, the scheme test of the first projection is
`T ×_H Hᵢ`; the assumed representable étale map represents this by a scheme étale over
`T`. (7) Represent a point of `G` by `Spec K → G`. Joint surjectivity lifts its image in
`H` to a member after a field extension. The two compatible sections give a section of
the sheaf fibre product over that extension, whose point maps to the original point.
For the empty index set the hypothesis forbids any target point, so the conclusion holds
also when both the index set and the pullback point sets are empty. -/
theorem etaleCover_pullback {S : Scheme.{u}} {I : Type w}
    (G H : AlgebraicSpace S) (Hᵢ : I → AlgebraicSpace S)
    (g : G ⟶ H) (h : ∀ i : I, Hᵢ i ⟶ H)
    (he : ∀ i : I, IsEtale (h i).hom.hom)
    (hs : IsJointlySurjective (fun i : I ↦ (h i).hom.hom)) :
    (∀ i : I, IsEtale (Limits.pullback.fst g.hom (h i).hom).hom) ∧
      IsJointlySurjective
        (fun i : I ↦ (Limits.pullback.fst g.hom (h i).hom).hom) := by
  sorry

/-- If the base-changed target is a scheme, the étale fibre product is a scheme.
Representability by a scheme is expressed as an isomorphism with its Yoneda presheaf.
Source: Stacks, Spaces, scheme-test definition of representable étale maps, Tag 025Y;
Topologies on Algebraic Spaces, Tag 041F(3)
(blueprint: lem-trf-space-fibre-products-etale-covers).
Proof: apply the representable étale scheme-test condition to the scheme representing
`G`, using its isomorphism to obtain the map to `H`. The representing pullback square
identifies its Yoneda presheaf with the sheaf fibre product `G ×_H H'`. -/
theorem etale_fibreProduct_isScheme {S : Scheme.{u}} (G H H' : AlgebraicSpace S)
    (g : G ⟶ H) (h : H' ⟶ H) (he : IsEtale h.hom.hom)
    (T : Over S) (e : G.obj.obj ≅ yoneda.obj T) :
    ∃ U : Over S, Nonempty ((Limits.pullback g.hom h.hom).obj ≅ yoneda.obj U) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
