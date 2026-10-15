module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

lemma chartExchange_finish
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (D.map j.hom).left
          (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V))
    (z' : (abelianHigherDirectImageRawPresheaf
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V))
    (hz : rawRestrictedCohomologyComparison
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (D.map j.hom).left
          (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V z = x)
    (hn : restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x =
      rawRestrictedCohomologyComparison
        (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
          pullback.snd f (D.obj i).hom) q
        (((pullback.snd (c.π.app i).left
            (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
          (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V z')
    (hraw : cartesianChartClassPullback (D.map j.hom).left (c.π.app j.left).left
        (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm
        V U r hr _ (q : ℤ)
        ((cartesianChartRawAdjunctionIso f (D.obj i).hom (D.map j.hom).left
          (D.obj j.left).hom (Over.w (D.map j.hom)).symm F q V).hom z) ≫
        (shiftFunctor _ (q : ℤ)).map
          (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
            (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso (c.π.app i).left V U r hr).hom ≫
        (cartesianChartRawAdjunctionIso f (D.obj i).hom (c.π.app i).left
          c.pt.hom (Over.w (c.π.app i)).symm F q V).hom z') :
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
  let := isIso_rawRestrictedCohomologyComparison
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
      pullback.snd f (D.obj i).hom) q
    (((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V
  have hzinv : rawRestrictedCohomologyClass
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (D.map j.hom).left
        (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V x = z := by
    apply (ConcreteCategory.bijective_of_isIso (rawRestrictedCohomologyComparison
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (D.map j.hom).left
        (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V)).1
    exact (rawRestrictedCohomologyClass_spec
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (D.map j.hom).left
        (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V x).trans hz.symm
  rw [hn]
  dsimp only [cartesianChartCohomologyLift]
  erw [hzinv]
  erw [chartCohomologyIso_eval f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr]
  exact hraw

end AlgebraicGeometry.Etale
