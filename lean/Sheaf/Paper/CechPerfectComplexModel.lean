/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.WeilCompletedKoszulSite
import all Sheaf.Paper.SfbPerfectModelComplexComparison
public import Sheaf.Paper.AdicPerfectModelCompleteReduction
import all Sheaf.Paper.AdicPerfectModelCompleteReduction
import all Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Sheaf.Paper.CompletedConstantCoefficientEquivalence
import all Sheaf.Paper.ProEtaleMultiplicationDifferenceCriterion

/-! # Perfect constant complexes in the intrinsic coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
namespace CechPerfectModel


private instance cechDown_equivalence (X : Scheme.{u}) :
    (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).IsEquivalence :=
  inferInstanceAs ((completedCechSiteEquiv X).inverse.IsEquivalence)

private instance cechDown_dense (X : Scheme.{u}) :
    (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).IsDenseSubsite
      (completedCechTopology X) (ProEt.topology X) := by
  change (completedCechSiteEquiv X).inverse.IsDenseSubsite
    ((completedCechSiteEquiv X).inverse.inducedTopology (ProEt.topology X)) _
  infer_instance

private instance cechDown_continuous (X : Scheme.{u}) :
    (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).IsContinuous
      (completedCechTopology X) (ProEt.topology X) := by infer_instance

private instance cechDown_cocontinuous (X : Scheme.{u}) :
    (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).IsCocontinuous
      (completedCechTopology X) (ProEt.topology X) := by infer_instance

private instance (priority := 10000) nativeAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} X

private instance (priority := 10000) nativeAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

private instance (priority := 10000) cechAbSheafify (X : Scheme.{u}) :
    HasSheafify (completedCechTopology X) AddCommGrpCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite.{u + 1, u + 1, u + 1, u + 2, u + 1} _ _

private instance (priority := 10000) cechAbLocallyBijective (X : Scheme.{u}) :
    (completedCechTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u + 1,
    u + 1, u + 1, u + 2, u + 1} _

private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private abbrev toSmall {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤ SheafOfModules.{u + 1}
      (((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (completedCechTopology X) (ProEt.topology X)).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := AsSmall.down.{u, u + 1, 0})
    (J := completedCechTopology X) (K := ProEt.topology X) (R := R) (𝟙 _)

private theorem cech_modelCoefficientMap (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (CechConstantAlgebra.pushRing X).map (CompletedConstantReduction.base X I) ≫
        (CechConstantAlgebra.completionIso X I).hom =
      (CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A) ≫
        ConstantCompletion.coefficientMap (completedCechTopology X) A I :=
  CechConstantAlgebra.coefficientMap_eq X I _
    (CompletedConstantReduction.base_exists X I).choose_spec.1

private abbrev cech_modelRing (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  ((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (completedCechTopology X) (ProEt.topology X)).obj R

section Sheafification

variable (X : Scheme.{u})
  {R₀ : X.ProEtᵒᵖ ⥤ RingCat.{u + 1}}
  {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
  (η : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective (ProEt.topology X) η]
  [Presheaf.IsLocallySurjective (ProEt.topology X) η]

private abbrev cech_modelUnit :=
  Functor.whiskerLeft (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).op η

attribute [-instance] SheafOfModules.instAbelian in
private instance cech_modelUnit_injective :
    Presheaf.IsLocallyInjective (completedCechTopology X) (cech_modelUnit X η) :=
  Presheaf.isLocallyInjective_whisker
    (completedCechTopology X) (ProEt.topology X) AsSmall.down.{u, u + 1, 0} η

attribute [-instance] SheafOfModules.instAbelian in
private instance cech_modelUnit_surjective :
    Presheaf.IsLocallySurjective (completedCechTopology X) (cech_modelUnit X η) :=
  Presheaf.isLocallySurjective_whisker
    (completedCechTopology X) (ProEt.topology X) AsSmall.down.{u, u + 1, 0} η

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelSheafificationSeed (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (_root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down.{u, u + 1, 0} R₀).obj M ⟶
      (_root_.PresheafOfModules.restrictScalars.{u + 1} (cech_modelUnit X η)).obj
        ((toSmall (X := X) R).obj ((_root_.PresheafOfModules.sheafification.{u +
            1} (J := ProEt.topology X) (R := R) η).obj
            M)).val where
  app U := (_root_.PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology X) (R
      := R) η).unit.app M |>.app
    (AsSmall.down.{u, u + 1, 0}.op.obj U)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact _root_.PresheafOfModules.naturality_apply
      ((_root_.PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology X) (R := R)
          η).unit.app M)
      (AsSmall.down.{u, u + 1, 0}.op.map f) x

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelSheafificationComparison (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (_root_.PresheafOfModules.sheafification.{u + 1} (J := completedCechTopology
        X)
      (R := cech_modelRing X R) (cech_modelUnit X η)).obj
        ((_root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down.{u, u + 1, 0} R₀).obj M) ⟶
      (toSmall (X := X) R).obj ((_root_.PresheafOfModules.sheafification.{u + 1}
          (J := ProEt.topology X) (R := R) η).obj M) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv.{u + 1} (J :=
      completedCechTopology X)
      (R := cech_modelRing X R) (cech_modelUnit X
      η)).symm
    (cech_modelSheafificationSeed X η M)

attribute [-instance] SheafOfModules.instAbelian in
private theorem cech_modelSheafificationComparison_underlying
    (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (SheafOfModules.toSheaf.{u + 1} (cech_modelRing X R)).map
      (cech_modelSheafificationComparison X η M) =
      (((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
          (completedCechTopology X) (ProEt.topology X)).hom.app
            M.presheaf) := by
  unfold cech_modelSheafificationComparison
  rw [_root_.PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((sheafificationAdjunction (completedCechTopology X)
    AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact ((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
      X.ProEt).toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u + 1}
      (completedCechTopology X) (ProEt.topology X) M.presheaf).symm

attribute [-instance] SheafOfModules.instAbelian in
private instance cech_modelSheafificationComparison_isIso
    (M : _root_.PresheafOfModules.{u + 1} R₀) :
    IsIso (cech_modelSheafificationComparison X η M) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{u + 1} (cech_modelRing X R)),
    cech_modelSheafificationComparison_underlying]
  infer_instance

attribute [local irreducible] cech_modelSheafificationComparison cech_modelSheafificationSeed

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelSheafificationIso :
    _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down.{u, u + 1, 0} R₀ ⋙
        _root_.PresheafOfModules.sheafification.{u + 1} (J := completedCechTopology X)
      (R := cech_modelRing X R) (cech_modelUnit X η) ≅
      _root_.PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology X) (R := R) η ⋙
          toSmall (X :=
          X) R := by
  refine NatIso.ofComponents (fun M ↦ asIso (cech_modelSheafificationComparison X η M)) ?_
  intro M N f
  apply (SheafOfModules.toSheaf.{u + 1} (cech_modelRing X R)).map_injective
  simp only [Functor.map_comp, asIso_hom, cech_modelSheafificationComparison_underlying]
  exact (((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (completedCechTopology X) (ProEt.topology X)).hom.naturality
        ((_root_.PresheafOfModules.toPresheaf.{u + 1} R₀).map f))

attribute [local irreducible] cech_modelSheafificationIso

end Sheafification

attribute [-instance] SheafOfModules.instAbelian in
private theorem cech_modelConstants_unitComm (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Functor.whiskerLeft
        (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))) ≫
      ((CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A)).hom =
    toSheafify (completedCechTopology X)
      ((Functor.const (completedCechSite X)ᵒᵖ).obj (CommRingCat.of A)) := by
  let e := ((AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (completedCechTopology X) (ProEt.topology X)).app
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  have h := (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤
      X.ProEt).toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (completedCechTopology X) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  change _ ≫ e.inv.hom = _
  rw [← h, Category.assoc]
  change _ ≫ (e.hom ≫ e.inv).hom = _
  rw [e.hom_inv_id]
  exact Category.comp_id _

attribute [local irreducible] CechConstantAlgebra.constantsIso CechConstantAlgebra.completionIso
attribute [local irreducible] moduleSheafificationComparison moduleSheafificationSeed

attribute [-instance] SheafOfModules.instAbelian in
private theorem cech_modelConstants_unit (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    cech_modelUnit X (R := adicLisseRing X A) (adicLisseConstantUnit X A) ≫
      ((sheafCompose (completedCechTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A))).hom =
      realizationRingUnit (completedCechTopology X) A := by
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (cech_modelConstants_unitComm X A)

private abbrev cech_actualConstantPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    _root_.PresheafOfModules.pushforward₀.{u + 1}
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelConstantPresheafIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    cech_actualConstantPresheaf X A ⋙
        _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down.{u, u + 1, 0}
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) ≅
      siteConstantModulePresheafGeneral (C := completedCechSite X) A :=
  NatIso.ofComponents (fun M ↦ _root_.PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)
    (by intros; rfl)) (by intros; rfl)

attribute [local irreducible] cech_modelConstantPresheafIso

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelConstantRingTransport (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    siteConstantModulePresheafGeneral (C := completedCechSite X) A ⋙
        _root_.PresheafOfModules.sheafification.{u + 1}
          (R := cech_modelRing X (adicLisseRing X A)) (cech_modelUnit X (R := adicLisseRing X A)
              (adicLisseConstantUnit X A)) ≅
      commutativeSiteConstantModuleFunctor (completedCechTopology X) A ⋙
        ConstantCompletion.res
          ((CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A)) := by
  let J := completedCechTopology X
  let ηA : (Functor.const (completedCechSite X)ᵒᵖ).obj (RingCat.of A) ⟶
      (cech_modelRing X (adicLisseRing X A)).obj :=
    cech_modelUnit X (R := adicLisseRing X A) (adicLisseConstantUnit X A)
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (realizationRing J A)
  let ηB := realizationRingUnit J A
  letI := (realizationRingUnit_locallyBijective J A).1
  letI := (realizationRingUnit_locallyBijective J A).2
  let α : cech_modelRing X (adicLisseRing X A) ⟶ B :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A))
  have h : ηA ≫ α.hom = ηB := cech_modelConstants_unit X A
  let Q := siteConstantModulePresheafGeneral (C := completedCechSite X) A
  change (Q ⋙ _root_.PresheafOfModules.sheafification.{u + 1} (J := J) (R := cech_modelRing X
      (adicLisseRing X A)) ηA) ≅
    Q ⋙ _root_.PresheafOfModules.sheafification.{u + 1} (J := J) (R := B) ηB ⋙
        SheafOfModules.restrictScalars α
  exact isoWhiskerLeft Q (moduleRingTransport J ηA ηB α h)

attribute [local irreducible] cech_modelConstantRingTransport

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelConstantModulesIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    adicLisseConstantModules X A ⋙ toSmall (X := X) (adicLisseRing X A) ≅
      commutativeSiteConstantModuleFunctor (completedCechTopology X) A ⋙
        ConstantCompletion.res ((CechConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A)) :=
  isoWhiskerLeft (cech_actualConstantPresheaf X A)
      (cech_modelSheafificationIso X (R := adicLisseRing X A) (adicLisseConstantUnit X A)).symm ≪≫
    isoWhiskerRight (cech_modelConstantPresheafIso X A)
      (_root_.PresheafOfModules.sheafification.{u + 1}
        (R := cech_modelRing X (adicLisseRing X A)) (cech_modelUnit X (R := adicLisseRing X A)
            (adicLisseConstantUnit X A))) ≪≫
    cech_modelConstantRingTransport X A

attribute [local irreducible] cech_modelConstantModulesIso

section ScalarExtension
variable (X : Scheme.{u})
  {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

attribute [-instance] SheafOfModules.instAbelian in
private def cech_modelScalarPresheafIso :
    actualScalarPresheaf X φ ⋙
        _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down.{u, u + 1, 0}
          ((adicLisseForget X).obj S).obj ≅
      toSmall (X := X) ((adicLisseForget X).obj R) ⋙
        SheafOfModules.RingedTensor.tensorPresheafFunctor
          ((CechConstantAlgebra.pushRing X).map φ) := by
  refine NatIso.ofComponents (fun M ↦ _root_.PresheafOfModules.isoMk
    (fun U ↦ (LinearEquiv.refl _ _).toModuleIso) ?_) ?_
  · intro U V f
    apply ModuleCat.ExtendScalars.hom_ext
      (R := R.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U))
      (S := S.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U))
    intro x
    change SheafOfModules.changeOfRingsMap φ M (AsSmall.down.{u, u + 1, 0}.op.map f)
      ((1 : S.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U)) ⊗ₜ[
        R.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U),
        (φ.hom.app (AsSmall.down.{u, u + 1, 0}.op.obj U)).hom] x) =
      SheafOfModules.changeOfRingsMap ((CechConstantAlgebra.pushRing X).map φ)
        ((toSmall (X := X) ((adicLisseForget X).obj R)).obj M) f _
    exact (SheafOfModules.changeOfRingsMap_tmul.{u, u + 1, u + 1}
      φ M (AsSmall.down.{u, u + 1, 0}.op.map f)
        (1 : S.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U)) x).trans
      (SheafOfModules.changeOfRingsMap_tmul.{u + 1, u + 1, u + 1}
        ((CechConstantAlgebra.pushRing X).map φ)
        ((toSmall (X := X) ((adicLisseForget X).obj R)).obj M)
        f (1 : S.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U)) x).symm
  · intro M N f
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
      (R := R.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U))
      (S := S.obj.obj (AsSmall.down.{u, u + 1, 0}.op.obj U))
    intro x
    rfl

attribute [local irreducible] cech_modelScalarPresheafIso

attribute [-instance] SheafOfModules.instAbelian
  cech_modelUnit_injective cech_modelUnit_surjective in
private def cech_modelScalarChangeIso :
    completedAdicChange X φ ⋙ toSmall (X := X) ((adicLisseForget X).obj S) ≅
      toSmall (X := X) ((adicLisseForget X).obj R) ⋙
        ConstantCompletion.change ((CechConstantAlgebra.pushRing X).map φ) := by
  let J := completedCechTopology X
  let T := cech_modelRing X ((adicLisseForget X).obj S)
  letI : Presheaf.IsLocallyInjective J (𝟙 T.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ h ↦ h)
  letI : Presheaf.IsLocallySurjective J (𝟙 T.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ x ↦ ⟨x, rfl⟩)
  exact isoWhiskerRight (actualScalarIso X φ) (toSmall (X := X) ((adicLisseForget
      X).obj S)) ≪≫
    isoWhiskerLeft (actualScalarPresheaf X φ)
      (cech_modelSheafificationIso X (R := (adicLisseForget X).obj S)
        (𝟙 ((adicLisseForget X).obj S).obj)).symm ≪≫
    isoWhiskerRight (cech_modelScalarPresheafIso X φ)
      (_root_.PresheafOfModules.sheafification.{u + 1}
        (J := completedCechTopology X)
        (R := cech_modelRing X ((adicLisseForget X).obj S))
        (𝟙 (cech_modelRing X ((adicLisseForget X).obj S)).obj))

attribute [local irreducible] cech_modelScalarChangeIso

end ScalarExtension

attribute [-instance] SheafOfModules.instAbelian in
private def cech_completedRealizationIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (I : Ideal A) :
    adicLisseConstantModules X A ⋙ completedAdicChange X (CompletedConstantReduction.base X I) ⋙
        toSmall (X := X) ((adicLisseForget X).obj (adicLisseCompletedRing X I)) ≅
      commutativeSiteConstantModuleFunctor (completedCechTopology X) A ⋙
        ConstantCompletion.change
          (ConstantCompletion.coefficientMap (completedCechTopology X) A I) ⋙
        ConstantCompletion.res (CechConstantAlgebra.completionIso X I).hom :=
  isoWhiskerLeft (adicLisseConstantModules X A)
      (cech_modelScalarChangeIso X (CompletedConstantReduction.base X I)) ≪≫
    isoWhiskerRight (cech_modelConstantModulesIso X A)
      (ConstantCompletion.change
        ((CechConstantAlgebra.pushRing X).map (CompletedConstantReduction.base X I))) ≪≫
    isoWhiskerLeft
      (commutativeSiteConstantModuleFunctor (completedCechTopology X) A)
      (scalarChangeSquare ((CechConstantAlgebra.constantsIso X).app (CommRingCat.of A))
        (CechConstantAlgebra.completionIso X I) _ _ (cech_modelCoefficientMap X I))

private theorem cech_slice_exact_products (X : Scheme.{u})
    (O : Sheaf (completedCechTopology X)
      CommRingCat.{u + 1}) (U : completedCechSite X) :
    CountableAB4Star
      (SheafOfModules.{u + 1} ((localCoefficientRings O).over U)) := by
  let J := completedCechTopology X
  let K := ProEt.topology X
  let d : completedCechSite X ≌ X.ProEt :=
    (AsSmall.equiv.{u, u + 1, 0} (C := X.ProEt)).symm
  let : (AsSmall.down.{u, u + 1, 0} : completedCechSite X ⥤ X.ProEt).IsEquivalence :=
    d.isEquivalence_functor
  have : d.functor.IsDenseSubsite J K := by
    change AsSmall.down.{u, u + 1, 0}.IsDenseSubsite
      (AsSmall.down.{u, u + 1, 0}.inducedTopology K) K
    infer_instance
  have : d.functor.IsCocontinuous J K := inferInstance
  have : d.inverse.IsCocontinuous K J := by
    apply (d.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
    exact Functor.IsDenseSubsite.coverPreserving J K d.functor
  let e₁ := Over.postEquiv (X := U) d
  have : e₁.functor.IsCocontinuous (J.over U) (K.over (d.functor.obj U)) :=
    inferInstanceAs ((Over.post d.functor).IsCocontinuous _ _)
  have : (Over.map (d.unitIso.inv.app U)).IsCocontinuous
      (J.over (d.inverse.obj (d.functor.obj U))) (J.over U) := by
    constructor
    intro V S hS
    change Sieve.overEquiv _ S ∈ J _ at hS
    change Sieve.overEquiv _ (S.functorPullback (Over.map (d.unitIso.inv.app U))) ∈ J _
    rwa [Sieve.overEquiv_functorPullback_map]
  have : e₁.inverse.IsCocontinuous (K.over (d.functor.obj U)) (J.over U) := by
    exact isCocontinuous_comp (Over.post d.inverse)
      (Over.map (d.unitIso.inv.app U)) (K.over (d.functor.obj U))
      (J.over (d.inverse.obj (d.functor.obj U)))
  have : e₁.inverse.IsDenseSubsite (K.over (d.functor.obj U)) (J.over U) :=
    e₁.isDenseSubsite_inverse_of_isCocontinuous _ _
  let W := d.functor.obj U
  let e₂ := ProEt.sliceEquiv X W
  have := ProEt.sliceDense X W
  let e := e₁.trans e₂
  let L := ProEt.topology W.left
  have : e.functor.IsCocontinuous (J.over U) L :=
    isCocontinuous_comp e₁.functor e₂.functor (J.over U) (K.over W)
  have : e.inverse.IsCocontinuous L (J.over U) :=
    isCocontinuous_comp e₂.inverse e₁.inverse L (K.over W)
  have : e.inverse.IsDenseSubsite L (J.over U) :=
    e.isDenseSubsite_inverse_of_isCocontinuous _ _
  let S := (e.inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    L (J.over U)).obj (O.over U)
  obtain ⟨q⟩ : Nonempty
      (SheafOfModules.{u + 1} ((localCoefficientRings O).over U) ≌
        SheafOfModules.{u + 1}
          ((sheafCompose L (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :=
    module_equivalence (J.over U) L e ((localCoefficientRings O).over U)
      ((sheafCompose L (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (Iso.refl _)
  let B := SheafOfModules.{u + 1}
    ((sheafCompose L (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  let : CountableAB4Star B :=
    AlgebraicGeometry.ProEtale.exact_countable_products.{u, 0} W.left S
  constructor
  intro I _
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete I) q.symm

/-- The finite-projective constant model on the intrinsic small site is complete.
Source: Bhatt--Scholze, Lemmas 6.5.8 and 6.6.8.
(blueprint: lem-weil-pbc-cech-perfect-complex-model).

Proof: exact countable products on each slice descend through the site equivalence.
The inverse-limit ring has invertible multiplication-difference maps, since the
scalar is nilpotent at each finite quotient. Finite-projective modules are retracts
of finite free modules; the generic ringed-ideal completeness criterion applies
termwise to the resulting complex. -/
theorem cech_model_complete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) :
    ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology T) A I 0)
      ((ConstantCompletion.Q _).obj (AdicPerfectModel.model (completedCechTopology T) I P)) := by
  let J := completedCechTopology T
  let R := ConstantCompletion.completed J A I
  refine AdicPerfectModel.complete_of_finite_retracts
    (ConstantCompletion.projection J A I 0)
    (fun U ↦ cech_slice_exact_products T R U) ?_ (AdicPerfectModel.model J I P) ?_
  · intro U f hf
    exact AdicPerfectModel.ringCone_difference
      (limit.cone (ConstantCompletion.finiteSystem J A I))
      (limit.isLimit _) U f
      (fun n ↦ AdicPerfectModel.projection_nilpotent I U f hf n.unop)
  · intro q
    have := (hP q).1
    have := (hP q).2
    exact AdicPerfectModel.model_retract (J := J) I (P.X q)

private def normalizedComparison (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (comparisonModulesEquiv T d).functor ≅
      pbcRestrict (pbcCompletedComparison T d).hom ⋙
        toSmall ((adicLisseForget T).obj (adicLisseCompletedRing T d.ideal)) ⋙
          ConstantCompletion.res (CechConstantAlgebra.completionIso T d.ideal).inv := by
  let F := (comparisonModulesEquiv T d).functor
  let G := pbcRestrict (pbcCompletedComparison T d).hom ⋙
    toSmall ((adicLisseForget T).obj (adicLisseCompletedRing T d.ideal)) ⋙
      ConstantCompletion.res (CechConstantAlgebra.completionIso T d.ideal).inv
  let f (M : pbcModules T (pbcAdicCompletion T d)) : F.obj M ⟶ G.obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).val.obj U) (Y := (G.obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := fun _ ↦ by ext x; rfl }⟩
  let g (M : pbcModules T (pbcAdicCompletion T d)) : G.obj M ⟶ F.obj M :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (G.obj M).val.obj U) (Y := (F.obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := fun _ ↦ by ext x; rfl }⟩
  exact NatIso.ofComponents (fun M ↦
    { hom := f M
      inv := g M
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (fun _ ↦ by ext U x; rfl)

attribute [local irreducible] normalizedComparison comparisonModulesEquiv

end CechPerfectModel
end AlgebraicGeometry.Scheme
