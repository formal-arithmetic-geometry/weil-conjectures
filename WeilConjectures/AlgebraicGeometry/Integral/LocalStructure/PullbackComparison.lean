/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import all WeilConjectures.AlgebraicGeometry.IntegralSectionLocalIsomorphisms
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions

/-! # Inverse image of the integral module realization

The realization of internal modules over the continuous integral coefficients as module
sheaves over the completed constant ring commutes with inverse image along any morphism of
schemes, up to an equivalence on the target.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage integralSectionRingIso
attribute [local instance] Scheme.proEtaleRingRestrictionPullbackInv_isIso
attribute [local instance 2000] Scheme.proEtaleRingModules_hasDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The realization of internal modules over the continuous integers as module sheaves over
the completed constant ring: the section functor followed by the coefficient comparisons.
This is `IntegralConstantModel.modulesFunctor` without its initial change of point ring.
(auxiliary; not a blueprint node). -/
abbrev integralRealization (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤
      Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) :=
  integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom ⋙
    Scheme.pbcRestrict (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom

/-- Inverse image of the integral realization along a morphism of schemes is, after an
equivalence of the target module categories, the internal inverse image.
(auxiliary; not a blueprint node). -/
theorem exists_integralRealization_pullback {X Y : Scheme.{u}} (h : Y ⟶ X) :
    ∃ Φ : AdicCompletion.Modules l E Y ⥤ Scheme.proEtaleRingModules Y
        ((Scheme.adicTowerInverseImage h).obj
          (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)),
      Φ.IsEquivalence ∧
        Nonempty (integralRealization l E X ⋙
            Scheme.proEtaleRingModulePullback h
              (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) _
              (Iso.refl _) ≅
          CondensedRing.upperStar (DerivedNakayama.integerRing l E) h ⋙ Φ) := by
  let d := Scheme.pbcIntegralDatum l E
  let Rs := Scheme.adicLisseCompletedRing X d.ideal
  let Rp := Scheme.pbcAdicCompletion X d
  let c := Scheme.pbcCompletedComparison X d
  let inv := Scheme.proEtaleSheafInverseImage h CommRingCat.{u + 1}
  obtain ⟨Q, ⟨e⟩⟩ := globalSectionComparison l E h
  let Res := restrictionEquivalence ((sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (Iso.refl (inv.obj Rp))).symm
  let b := inverseImageRingedComparison h Rp (inv.obj Rp) (Iso.refl _)
  let r := asIso (Scheme.proEtaleRingRestrictionPullbackInv h Rs Rp (inv.obj Rs) (inv.obj Rp)
    c.hom (inv.map c.hom) (Iso.refl _) (Iso.refl _) (by
      exact (Category.id_comp _).trans (Category.comp_id _).symm))
  have hc : (Scheme.proEtaleRingRestrictScalars (inv.map c.hom)).IsEquivalence :=
    restriction_isEquivalence ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (inv.mapIso c))
  refine ⟨Q.functor ⋙ Res.functor ⋙ Scheme.proEtaleRingRestrictScalars (inv.map c.hom),
    inferInstance, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft (integralSectionFunctor l E X ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom) r ≪≫
    Functor.isoWhiskerLeft (integralSectionFunctor l E X ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom)
      (Functor.isoWhiskerRight b.symm _) ≪≫
    Functor.isoWhiskerRight e.symm (Res.functor ⋙
      Scheme.proEtaleRingRestrictScalars (inv.map c.hom))

/-- Changing the point ring to the continuous integers and back is the identity on modules.
(auxiliary; not a blueprint node). -/
def pointComparisonRoundTrip (X : Scheme.{u}) :
    Mod.comap (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X) ⋙
        Mod.comap (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X) ≅
      𝟭 (AdicCompletion.Modules l E X) :=
  (Mod.comapComp _ _).symm ≪≫
    Mod.comapCongr (by
      rw [← coefficientMap_comp, ← Mon.comp_hom', Iso.hom_inv_id, Mon.id_hom',
        coefficientMap_id]) ≪≫
    Mod.comapId _

/-- The derived inverse image of the transported realization of `K` is, after an equivalence
of the target derived categories, the internal derived inverse image of `K`.
(auxiliary; not a blueprint node). -/
theorem exists_derived_integralRealization_pullback {X Y : Scheme.{u}} (h : Y ⟶ X) :
    ∃ (Φ : AdicCompletion.Modules l E Y ⥤ Scheme.proEtaleRingModules Y
        ((Scheme.adicTowerInverseImage h).obj
          (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)))
      (_ : Φ.IsEquivalence) (_ : Φ.Additive),
      (Nonempty (integralRealization l E X ⋙
            Scheme.proEtaleRingModulePullback h
              (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) _
              (Iso.refl _) ≅
          CondensedRing.upperStar (DerivedNakayama.integerRing l E) h ⋙ Φ)) ∧
      ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
        Nonempty ((Scheme.adicTowerPullback h
            (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)).obj
            ((IntegralConstantModel.derived l E X).functor.obj
              ((Mod.comap (coefficientMap
                (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj
                  K)) ≅
          Φ.mapDerivedCategory.obj
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) h).mapDerivedCategory.obj
              K)) := by
  obtain ⟨Φ, hΦ, ⟨α⟩⟩ := exists_integralRealization_pullback l E h
  have : Φ.Additive := Functor.additive_of_preserves_binary_products _
  refine ⟨Φ, hΦ, this, ⟨α⟩, fun K ↦ ⟨?_⟩⟩
  let F₁ := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let F₂ := IntegralConstantModel.modulesFunctor l E X
  let F₃ := Scheme.proEtaleRingModulePullback h
    (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) _ (Iso.refl _)
  let β : F₁ ⋙ F₂ ⋙ F₃ ≅
      CondensedRing.upperStar (DerivedNakayama.integerRing l E) h ⋙ Φ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pointComparisonRoundTrip l E X) _ ≪≫
          Functor.leftUnitor _) F₃ ≪≫ α
  exact (Functor.mapDerivedCategoryCompIso F₂ F₃).app (F₁.mapDerivedCategory.obj K) ≪≫
    (Functor.mapDerivedCategoryCompIso F₁ (F₂ ⋙ F₃)).app K ≪≫
    (Functor.mapDerivedCategoryNatIso β).app K ≪≫
    ((Functor.mapDerivedCategoryCompIso _ Φ).app K).symm

end AlgebraicGeometry.ProEtale
