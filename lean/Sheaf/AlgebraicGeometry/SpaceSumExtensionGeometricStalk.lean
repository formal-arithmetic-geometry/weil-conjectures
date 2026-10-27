module

public import Sheaf.AlgebraicGeometry.SpaceStructureModuleSumExtension
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Geometric stalks of structure-module étale sum extension

Source: Stacks Project, spaces-perfect.tex, Tag 08GU, equations stalk-restriction
and stalk-j-shriek; sites-modules.tex, Tag 0710, including its germ construction
(blueprint: lem-sfb-space-sum-extension-geometric-stalk).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

open Classical in
/-- Geometric stalks of sum extension decompose canonically as the sum over lifts.
The first clause concerns the actual structural ring map. The unique family of
linear equivalences is normalized on every scheme-chart germ and natural in M.

Source: Stacks Project, Tag 08GU, equations stalk-restriction and stalk-j-shriek;
Tag 0710, lemma-stalk-j-shriek
(blueprint: lem-sfb-space-sum-extension-geometric-stalk).

Proof:
1. Étale localization identifies the restricted structure sheaf with O_Z
(lem-trf-space-enlarged-etale-ringed-site-model). The geometric-point comparison
(lem-sfb-space-geometric-points-conservative) identifies its stalk with O_X,x.
Thus every specified structural stalk map is an isomorphism.
2. The summed presheaf has the displayed restrictions; étale cancellation makes
all lift charts legal (lem-trf-space-chartwise-etale-permanence). Pointed scheme
neighbourhoods are cofiltered (lem-sfb-space-pointed-etale-neighbourhoods-cofiltered).
An étale cover lifts each geometric point (lem-weil-pbc-etale-cover-geometric-point-lift).
Hence the site-point abelian sheafification comparison
(lem-sfb-site-point-abelian-sheafification-fibre) identifies its colimit with the
stalk of module sheafification. The sheafification unit is module-linear.
3. Send a germ represented in the a-summand on (W,w) to its germ in the a w-summand.
Restriction keeps this germ unchanged, including when labels merge, so the colimit
universal property (def-weil-pbc-category-colimit) gives a homomorphism.
4. Conversely, compose each pointed chart over a source lift with j, include its
section in that lift summand, then take its target germ. These compatible maps
induce a map from each source stalk and hence from their direct sum.
5. The two composites are the identity on section germs, hence everywhere by the
colimit and direct-sum universal properties. Represent a scalar and a section on
one common pointed refinement. The germ formula commutes with their product, so
both maps are linear for the specified structural scalar restriction. Elementwise
representatives are supplied by lem-weil-pbc-filtered-colimit-modules-elementwise
with R = Z on the additive diagrams. Module morphisms commute with every germ
map, giving the naturality equation. The affine basis is cofinal, so the existing
normalized stalk models and the arbitrary-chart germs give exactly this colimit.
Empty lift sets give zero; all sums have finite support, with no finite-fibre,
nonemptiness, separation or quasi-compactness hypothesis. -/
theorem spaceSumExtension_geometricStalk (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    (∀ a : SumLift j x, Function.Bijective (spaceSumStalkScalar j s x a)) ∧
    ∃! e : ∀ M : Z.Modules,
      (SingleComplex.stalkModel s x).modules.obj (spaceSumExtension j hj M) ≃ₗ[
        SingleComplex.stalkRing s x]
        DirectSum (SumLift j x) (fun a ↦ spaceSumStalkPiece j s x M a),
      (∀ (M : Z.Modules) (W : X.PointedEtale x) (a : SumLift j W.right.obj.hom)
        (m : M.val.obj (op (sumLiftChart j hj W.right a))),
        e M (spaceChartGerm s x (spaceSumExtension j hj M) W
          (spaceSumGenerator j hj M W.right a m)) =
          DirectSum.of (fun b ↦ spaceSumStalkPiece j s x M b) (spaceSumPointLift j x W a)
            (spaceChartGerm s (yonedaEquiv.symm (spaceSumPointLift j x W a).val) M
              (spaceSumLiftPointed j hj x W a) m)) ∧
      (∀ (M N : Z.Modules) (f : M ⟶ N)
        (v : (SingleComplex.stalkModel s x).modules.obj (spaceSumExtension j hj M)),
        e N ((SingleComplex.stalkModel s x).modules.map (spaceSumExtensionHom j hj f) v) =
          DirectSum.lmap (fun a ↦
            ((ModuleCat.restrictScalars (spaceSumStalkScalar j s x a)).map
              ((SingleComplex.stalkModel s (yonedaEquiv.symm a.val)).modules.map f)).hom)
            (e M v)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
