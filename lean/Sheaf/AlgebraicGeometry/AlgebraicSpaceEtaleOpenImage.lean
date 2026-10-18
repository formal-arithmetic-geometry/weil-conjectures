/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Open images of representable étale morphisms of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03BX, 03BZ, 03IR, 03H4, 03H5, 03E4
(blueprint: lem-a1-space-etale-open-image).

The open subspace is an actual subfunctor, so pullback is its literal subfunctor preimage.
All image equalities refer to field-valued point classes. Surjectivity is tested on schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.AlgebraicSpace

/-- The topology is the quotient topology of any representable surjective étale scheme
atlas. Source: Stacks, Tag 03BX (blueprint: lem-a1-space-etale-open-image).
Proof: refine two atlases by their scheme fibre product using
lem-trf-space-fibre-products-etale-covers. Its projections are étale and surjective,
hence open quotient maps of schemes. The common-field point calculation (Tag 03H4)
identifies inverse images, so the two atlas quotient topologies agree. Every étale
scheme-source map is continuous for this topology by the same comparison, hence the
final topology for all such maps is exactly the topology of a single atlas. This is
step 2 of the node, using lem-a1-space-affine-etale-cover. -/
theorem points_atlas_isOpen_iff {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj)
    (he : IsEtale a) (hs : IsSurjective a) (O : Set (Point F.obj.obj)) :
    IsOpen O ↔ IsOpen (schemePointMap a ⁻¹' O) := by
  sorry

/-- Open subspaces correspond to open subsets, preserving and reflecting inclusion.
Source: Stacks, Tag 03BZ (blueprint: lem-a1-space-etale-open-image).
Proof (steps 1--5): the common-field calculation identifies point images under fibre
products (lem-trf-space-fibre-products-etale-covers). An open subspace pulls back along
an atlas to an open subscheme, and its points have the subspace topology by the quotient
criterion (lem-a1-space-affine-etale-cover). For an open subset `O`, pull it back to an
invariant open `V` of an atlas `U`. In the presentation `R = U ×_F U` of
lem-a1-etale-atlas-presentation, the opens `s⁻¹(V)` and `t⁻¹(V)` agree. Restrict the
relation to `V`; its projections remain étale by lem-weil-pbc-etale-scheme-base-change.
The quotient of this relation is an algebraic space by lem-trf-etale-relation-quotient,
and its map to `F` is an open immersion by lem-trf-etale-relation-finding-opens (open
immersions are étale by lem-weil-pbc-etale-composition-cancellation). Its point image
is `O`. Finally, inclusion of point subsets forces inclusion of subfunctors: on any
scheme test, the relevant open immersion has full point image and is an isomorphism.
This proves uniqueness and both directions of the order correspondence. -/
theorem openSubspace_points_orderIso {S : Scheme.{u}} (F : AlgebraicSpace S) :
    ∃ e : OpenSubspace F ≃o Opens (Point F.obj.obj),
      ∀ A : OpenSubspace F, (e A : Set (Point F.obj.obj)) = pointImage A.val.ι := by
  sorry

/-- The open point image of a representable étale map is an open subspace, with a
representable surjective étale factorization; its open image commutes with arbitrary
base change, and is quasi-compact when the source point space is quasi-compact.
Source: Stacks, Tags 03IR, 03H4, 03H5, 03E4
(blueprint: lem-a1-space-etale-open-image).
Proof (steps 6--9): compose `q` with an atlas of `E`. The composite is representable
étale by lem-weil-pbc-etale-composition-cancellation, and its open point image equals
that of `q` by the point-surjectivity of the atlas (lem-a1-space-affine-etale-cover).
The open-subspace correspondence constructs `A`. Its pullback to `E` is an open
subspace with full point image, hence is all of `E`; this gives the factorization.
Since `A → F` is monic, each scheme test of the factor is the corresponding scheme
test of `q`, so it is étale. Surjectivity follows by the common-field calculation
and scheme tests (Tags 03H4, 03H5). For arbitrary `g`,
lem-trf-space-fibre-products-etale-covers supplies the algebraic-space pullback;
its point image is the inverse image of the point image of `q`, as is the open
subfunctor preimage of `A`. Uniqueness of open subspaces proves the asserted identity.
Finally the continuous surjection from `|E|` to `|A|` sends a finite subcover of the
pulled-back open cover to a finite subcover, proving quasi-compactness. -/
theorem etale_open_image {S : Scheme.{u}} (E F : AlgebraicSpace S) (q : E ⟶ F)
    (hq : IsEtale q.hom.hom) :
    IsOpen (pointImage q.hom.hom) ∧
      ∃ A : OpenSubspace F,
        pointImage q.hom.hom = pointImage A.val.ι ∧
        (∃ qI : E.obj.obj ⟶ A.val.toFunctor,
          qI ≫ A.val.ι = q.hom.hom ∧ IsEtale qI ∧ IsSurjective qI) ∧
        (∀ (G : AlgebraicSpace S) (g : G ⟶ F),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
            (A.val.preimage g.hom.hom).ι ∧
          pointImage (Limits.pullback.snd q.hom g.hom).hom =
            pointImage (A.val.preimage g.hom.hom).ι) ∧
        (CompactSpace (Point E.obj.obj) → CompactSpace (Point A.val.toFunctor)) := by
  sorry

/-- Topological quasi-compactness is equivalent to the existence of a quasi-compact
scheme atlas. Source: Stacks, Tag 03E4 (blueprint: lem-a1-space-etale-open-image).
Proof (steps 9--10): an atlas gives a continuous surjection on point spaces, so
quasi-compactness descends by pulling back open covers. Conversely refine an atlas to
a disjoint union of affine schemes using lem-a1-space-affine-etale-cover and
lem-weil-pbc-scheme-coproduct-family. The images of the affine components are open
and cover. Select finitely many by quasi-compactness; their union is quasi-compact by
lem-weil-pbc-affine-scheme-qcqs and is still an étale scheme-source map by
lem-weil-pbc-etale-composition-cancellation. It is point-surjective, hence surjective
on scheme tests by Tag 03H5. If the space is empty, take the empty finite union. -/
theorem points_compactSpace_iff {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    CompactSpace (Point Z.obj.obj) ↔
      ∃ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
        CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
