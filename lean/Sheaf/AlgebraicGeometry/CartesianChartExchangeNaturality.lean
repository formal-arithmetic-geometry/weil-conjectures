/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Naturality of the specified chart comparisons under exchange

Source: Stacks Project, Tag 0EYM, second proof, commutativity of its comparison square.
-/

@[expose] public section


universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem cartesianChartAdjunct_spec {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g')).derivedPlus.homEquiv _ _
        ((cartesianChartAdjunctIso f g a g' w F q V).hom z) ≫
          (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}]).commShiftIso
            (q : ℤ)).hom.app _ =
      (cartesianChartRawAdjunctionIso f g a g' w F q V).hom z := by
  rfl


/-- The explicit chart lift and apex isomorphism commute with the specified
cartesian derived exchange. This asserts an identity between constructed maps;
it does not choose an isomorphism, lift, coefficient object, or representative.
Source: Stacks Project, Tags 0EYM, 03Q8, 03CB and 09YQ.
(blueprint: lem-sc-cartesian-chart-exchange-naturality).

Proof: Apply rawRestrictedCohomologyComparison_naturality to the chart cone leg
with its upperStarComp coefficient map. It identifies the inverse evaluation of
the restricted cohomology map with abelianHigherDirectImageRawPullback of the
stage class. Expand cartesianChartRawAdjunctionIso on both sides. Pullback
uniqueness identifies the two arrows from the actual apex source to the chart
stage: the inverse chart identification followed by the chart leg equals the
cartesian projection followed by the inverse stage identification. Each equality
is checked after the two pullback projections. Inverse-image composition then
identifies the coefficient maps and the free-sheaf source maps; its associativity
and naturality cancel the chart identifications. Take derived adjoints under the
apex projection. Replace derivedBaseChangeMapPlus by its mate using
baseChange_eq_derivedBaseChangeMapPlus. The adjunction triangle identity cancels
the stage counit with its unit, leaving exactly the pullback of the raw stage
class followed by the coefficient comparison. Naturality of the single-functor
and shift comparisons identifies these factors with the definition of
abelianHigherDirectImageRawPullback. Undoing the raw evaluation comparison proves
the equation. The free-sheaf source is transported by the specified pullback
square hr throughout; no invertibility of exchange is used. Empty test objects
and q=0 require no separate argument. -/
theorem cartesianChartCohomologyLift_exchange
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    cartesianChartCohomologyLift f D c F q i V U r hr j x ≫
      (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
          (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
    (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V U r hr).hom
      (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) := by
  sorry

end AlgebraicGeometry.Etale
