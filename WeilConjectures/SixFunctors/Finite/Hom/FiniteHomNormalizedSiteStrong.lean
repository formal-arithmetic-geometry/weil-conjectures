/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicTensor
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicChainTensor
import all WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientKFlatReflection
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Strong core for the normalized finite-Hom site comparison

This is the core-construction half of the normalized site comparison law.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b c d h ha hb hc aU bU
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local instance] ProEtale.finiteCoefficientIntrinsicMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory
private theorem smallCache (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _
attribute [local instance] smallCache
private theorem abSheafifyCache (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
attribute [local instance] abSheafifyCache
private theorem abBijectiveCache (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

attribute [local instance] abBijectiveCache
@[instance_reducible] private def targetDerivedCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _
attribute [local instance] targetDerivedCache
@[instance_reducible] private def sourceDerivedCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  inferInstance
attribute [local instance] sourceDerivedCache
@[instance_reducible] private def nativeTarget (X : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalCategory (DerivedCategory.{u + 2}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))) :=
  RingedDerivedNative.monoidal.{u + 1, u, u, u + 2} (ProEt.topology X)
    (Scheme.proEtaleConstantRing X A)
attribute [local instance] nativeTarget
private theorem targetGrothCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u + 1}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  ConstantScalarRestriction.ringGrothendieck (ProEt.topology X) (ULift.{u + 1, u} A)
attribute [local instance] targetGrothCache
@[instance_reducible] private def targetClosedCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalClosed (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  ConstantScalarRestriction.ringClosed (ProEt.topology X) (ULift.{u + 1, u} A)
attribute [local instance] targetClosedCache
private theorem targetFlatCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian.HasFunctorialFlatResolution
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  ConstantScalarRestriction.ringFlatResolutions (ProEt.topology X) (ULift.{u + 1, u} A)
attribute [local instance] targetFlatCache
private theorem sourceGrothCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  ConstantScalarRestriction.fixedGrothendieck X.smallEtaleTopology (ULift.{u + 1, u} A)
attribute [local instance] sourceGrothCache
@[instance_reducible] private def sourceClosedCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalClosed (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  ConstantScalarRestriction.fixedClosed X.smallEtaleTopology (ULift.{u + 1, u} A)
attribute [local instance] sourceClosedCache
private theorem sourceFlatCache (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian.HasFunctorialFlatResolution (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  ConstantScalarRestriction.fixedFlatResolutions X.smallEtaleTopology (ULift.{u + 1, u} A)

attribute [local instance] sourceFlatCache
section
variable (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
private theorem gColimits : PreservesColimitsOfSize.{0, 0}
    (ProEtale.finiteCoefficientIntrinsicComparison X A) := ProEtale.nu_preservesColimits X A
attribute [local instance] gColimits
omit [Finite A] in
private theorem gradedCache : ∀ (M N : GradedObject ℤ
    (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))), M.HasTensor N :=
  RingedKFlatModel.gradedTensorCache.{u + 1, u, u} (ProEt.topology X)
    (Scheme.proEtaleConstantRing X A)
omit [Finite A] in
private theorem gradedFourCache : ∀ (M N P Q : GradedObject ℤ
    (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))),
    GradedObject.HasTensor₄ObjExt M N P Q :=
  RingedKFlatModel.gradedTensorFourCache.{u + 1, u, u} (ProEt.topology X)
    (Scheme.proEtaleConstantRing X A)
omit [Finite A] in
private theorem gradedLeftCache : ∀ (M N P : GradedObject ℤ
    (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))),
    GradedObject.HasGoodTensor₁₂Tensor M N P :=
  RingedKFlatModel.gradedTensorLeftCache.{u + 1, u, u} (ProEt.topology X)
    (Scheme.proEtaleConstantRing X A)
omit [Finite A] in
private theorem gradedRightCache : ∀ (M N P : GradedObject ℤ
    (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))),
    GradedObject.HasGoodTensorTensor₂₃ M N P :=
  RingedKFlatModel.gradedTensorRightCache.{u + 1, u, u} (ProEt.topology X)
    (Scheme.proEtaleConstantRing X A)
attribute [local instance 10000] gradedCache gradedFourCache gradedLeftCache gradedRightCache
omit [Finite A] in
private theorem tensorLeftCache (M : Scheme.proEtaleRingModules X
    (Scheme.proEtaleConstantRing X A)) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (Scheme.proEtaleConstantRing X A) M
attribute [local instance] tensorLeftCache
omit [Finite A] in
private theorem tensorRightCache (M : Scheme.proEtaleRingModules X
    (Scheme.proEtaleConstantRing X A)) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits (Scheme.proEtaleConstantRing X A) M
attribute [local instance] tensorRightCache
end
attribute [local instance] gColimits tensorLeftCache tensorRightCache
attribute [local instance 10000] gradedCache gradedFourCache gradedLeftCache gradedRightCache
section
private theorem monoidalOfInverseUnit
    {C : Type aU} {D : Type bU} [Category.{ha} C] [Category.{hb} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (e : D ≌ C) [e.functor.Monoidal] (F : C ⥤ D)
    (η : 𝟭 C ≅ F ⋙ e.functor) :
    ∃ m : F.Monoidal, letI := m; NatTrans.IsMonoidal η.hom := by
  let : e.inverse.Monoidal := e.inverseMonoidal
  have : e.IsMonoidal := by infer_instance
  let adj := e.symm.toAdjunction
  let b : (𝟭 C) ⋙ e.inverse ≅ F :=
    Functor.isoWhiskerRight η e.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  let : F.LaxMonoidal := Functor.LaxMonoidal.transport b
  have : IsIso (Functor.LaxMonoidal.ε F) := by
    change IsIso (Functor.LaxMonoidal.ε ((𝟭 C) ⋙ e.inverse) ≫ b.hom.app _)
    infer_instance
  have (X Y : C) : IsIso (Functor.LaxMonoidal.μ F X Y) := by
    change IsIso ((b.inv.app X ⊗ₘ b.inv.app Y) ≫
      Functor.LaxMonoidal.μ ((𝟭 C) ⋙ e.inverse) X Y ≫ b.hom.app (X ⊗ Y))
    infer_instance
  let : F.Monoidal := ConstantScalarRestriction.monoidalKeepingLax F
  refine ⟨inferInstance, ?_⟩
  exact ConstantScalarRestriction.monoidalMate (𝟭 C) F e.inverse e.functor adj η
private theorem inverseUnit_tensor
    {C : Type aU} {D : Type bU} [Category.{ha} C] [Category.{hb} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [R.Monoidal] [F.Monoidal]
    (η : 𝟭 C ≅ F ⋙ R) [NatTrans.IsMonoidal η.hom] (X Y : C) :
    η.hom.app (X ⊗ Y) ≫ R.map (Functor.OplaxMonoidal.δ F X Y) =
      (η.hom.app X ⊗ₘ η.hom.app Y) ≫
        Functor.LaxMonoidal.μ R (F.obj X) (F.obj Y) := by
  have h := NatTrans.IsMonoidal.tensor (τ := η.hom) X Y
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp,
    Functor.LaxMonoidal.comp_μ] at h
  rw [h]
  simp only [Category.assoc, ← R.map_comp, Functor.Monoidal.μ_δ,
    R.map_id, Category.comp_id]

private theorem fixedPure_map (X : Scheme.{u}) (A : Type u) [CommRing A]
    {M N M' N' : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.ProEtᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    (f ⊗ₘ g).hom.app U
        (ConstantScalarRestriction.fixedPure (ProEt.topology X)
          (ULift.{u + 1, u} A) M N U x y) =
      ConstantScalarRestriction.fixedPure (ProEt.topology X) (ULift.{u + 1, u} A)
        M' N' U (f.hom.app U x) (g.hom.app U y) := by
  let i := sheafToPresheaf (ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  have h := Functor.LaxMonoidal.μ_natural i f g
  have hh := congrArg (fun z ↦ z.app U (x ⊗ₜ y)) h
  exact hh.symm

variable (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
omit [Finite A] in
private theorem scalarUnit_eq :
    ConstantScalarRestriction.scalarUnit (ProEt.topology X) (ULift.{u + 1, u} A) =
      Scheme.proEtaleModuleScalarUnit X A := by
  unfold ConstantScalarRestriction.scalarUnit Scheme.proEtaleModuleScalarUnit
  unfold constantCommuteCompose
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv]
  change toSheafify (ProEt.topology X) _ ≫
    (sheafifyMap (ProEt.topology X)
      (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of (ULift.{u + 1, u} A))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
      (sheafifyComposeIso (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafComposeIso_hom_fac]
  ext U
  simp
private def restrictionOriginObjIso
    (M : ConstantScalarRestriction.Modules (ProEt.topology X) (ULift.{u + 1, u} A)) :
    (ConstantScalarRestriction.restriction (ProEt.topology X)
      (ULift.{u + 1, u} A)).obj M ≅ (Scheme.proEtaleModuleRestriction X A).obj M := by
  refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
  · refine ⟨{ app := ?_, naturality := ?_ }⟩
    · intro U
      exact ModuleCat.ofHom
        (X := ((ConstantScalarRestriction.restriction (ProEt.topology X)
          (ULift.{u + 1, u} A)).obj M).obj.obj U)
        (Y := ((Scheme.proEtaleModuleRestriction X A).obj M).obj.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun b x ↦ by
            change ((M.val.obj U).smul
                (((ConstantScalarRestriction.scalarUnit (ProEt.topology X)
                  (ULift.{u + 1, u} A)).app U).hom b)).hom x =
              ((M.val.obj U).smul (((Scheme.proEtaleModuleScalarUnit X A).app U).hom b)).hom x
            rw [scalarUnit_eq]
            rfl }
    · intro U V f
      ext x
      rfl
  · refine ⟨{ app := ?_, naturality := ?_ }⟩
    · intro U
      exact ModuleCat.ofHom
        (Y := ((ConstantScalarRestriction.restriction (ProEt.topology X)
          (ULift.{u + 1, u} A)).obj M).obj.obj U)
        (X := ((Scheme.proEtaleModuleRestriction X A).obj M).obj.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun b x ↦ by
            change ((M.val.obj U).smul
                (((Scheme.proEtaleModuleScalarUnit X A).app U).hom b)).hom x =
              ((M.val.obj U).smul (((ConstantScalarRestriction.scalarUnit (ProEt.topology X)
                (ULift.{u + 1, u} A)).app U).hom b)).hom x
            rw [scalarUnit_eq]
            rfl }
    · intro U V f
      ext x
      rfl
  · ext U x
    rfl
  · ext U x
    rfl
private def restrictionOriginIso :
    ConstantScalarRestriction.restriction (ProEt.topology X) (ULift.{u + 1, u} A) ≅
      Scheme.proEtaleModuleRestriction X A :=
  NatIso.ofComponents (restrictionOriginObjIso X A) (by intro M N f; ext U x; rfl)
private def originUnit :
    𝟭 (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶
      ProEtale.finiteCoefficientIntrinsicRealization X A ⋙
        Scheme.proEtaleModuleRestriction X A where
  app M := ProEtale.realizationRestrictionUnit X A M
  naturality M N f := by
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.app U)
        ((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
            ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
              (ULift.{u + 1, u} A)).map f.hom))) x
private def realizationUnitIso :
    𝟭 (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≅
      ProEtale.finiteCoefficientIntrinsicRealization X A ⋙
        ConstantScalarRestriction.restriction (ProEt.topology X) (ULift.{u + 1, u} A) := by
  have (M : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) : IsIso ((originUnit X A).app M) :=
    ProEtale.realizationRestrictionUnit_isIso X A M
  haveI : IsIso (originUnit X A) := by
    rw [NatTrans.isIso_iff_isIso_app]
    infer_instance
  exact asIso (originUnit X A) ≪≫
    Functor.isoWhiskerLeft _ (restrictionOriginIso X A).symm
private theorem realizationMonoidal :
    ∃ m : (ProEtale.finiteCoefficientIntrinsicRealization X A).Monoidal,
      letI := m
      ∀ (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
        (U : X.ProEtᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U),
      (Functor.OplaxMonoidal.δ (ProEtale.finiteCoefficientIntrinsicRealization X A)
        M N).val.app U
        (ProEtale.intrinsicSection X A (M ⊗ N) U
          (ConstantScalarRestriction.fixedPure (ProEt.topology X)
            (ULift.{u + 1, u} A) M N U x y)) =
        ProEtale.intrinsicPure X A
          ((ProEtale.finiteCoefficientIntrinsicRealization X A).obj M)
          ((ProEtale.finiteCoefficientIntrinsicRealization X A).obj N) U
          (ProEtale.intrinsicSection X A M U x) (ProEtale.intrinsicSection X A N U y) := by
  let F := ProEtale.finiteCoefficientIntrinsicRealization X A
  let R := ConstantScalarRestriction.restriction (ProEt.topology X) (ULift.{u + 1, u} A)
  let η := realizationUnitIso X A
  let : (ConstantScalarRestriction.restriction (ProEt.topology X)
      (ULift.{u + 1, u} A)).Monoidal :=
    (ConstantScalarRestriction.ordinary (ProEt.topology X)
      (ULift.{u + 1, u} A)).braided.toMonoidal
  let : R.Monoidal := inferInstanceAs (ConstantScalarRestriction.restriction
    (ProEt.topology X) (ULift.{u + 1, u} A)).Monoidal
  let : R.asEquivalence.functor.Monoidal := inferInstanceAs R.Monoidal
  obtain ⟨m, hm⟩ := monoidalOfInverseUnit R.asEquivalence F η
  let : (ProEtale.finiteCoefficientIntrinsicRealization X A).Monoidal := m
  let : F.Monoidal := m
  have : NatTrans.IsMonoidal η.hom := hm
  refine ⟨m, ?_⟩
  intro M N U x y
  have h := inverseUnit_tensor F R η M N
  have hh := congrArg (fun f ↦ f.hom.app U
    (ConstantScalarRestriction.fixedPure (ProEt.topology X)
      (ULift.{u + 1, u} A) M N U x y)) h
  change (Functor.OplaxMonoidal.δ F M N).val.app U
      (ProEtale.intrinsicSection X A (M ⊗ N) U
        (ConstantScalarRestriction.fixedPure (ProEt.topology X)
          (ULift.{u + 1, u} A) M N U x y)) =
    (Functor.LaxMonoidal.μ R (F.obj M) (F.obj N)).hom.app U
      ((η.hom.app M ⊗ₘ η.hom.app N).hom.app U
        (ConstantScalarRestriction.fixedPure (ProEt.topology X)
          (ULift.{u + 1, u} A) M N U x y)) at hh
  have hp := fixedPure_map X A (η.hom.app M) (η.hom.app N) U x y
  have hp' := congrArg (fun z ↦
    (Functor.LaxMonoidal.μ R (F.obj M) (F.obj N)).hom.app U z) hp
  exact hh.trans (hp'.trans ((ConstantScalarRestriction.ordinary (ProEt.topology X)
    (ULift.{u + 1, u} A)).tensor_inv (F.obj M) (F.obj N) U
      (ProEtale.intrinsicSection X A M U x) (ProEtale.intrinsicSection X A N U y)))
private theorem ordinarySiteMonoidal :
    ∃ m : (ProEtale.finiteCoefficientIntrinsicComparison X A).Monoidal,
      letI := m
      ProEtale.FiniteCoefficientTensorNormalization X A
        (Functor.Monoidal.μNatIso (ProEtale.finiteCoefficientIntrinsicComparison X A)).symm ∧
      (ProEtale.finiteCoefficientIntrinsicComparison X A).PreservesFlat := by
  obtain ⟨mF, hF⟩ := realizationMonoidal X A
  let := mF
  let F := ProEtale.finiteCoefficientIntrinsicRealization X A
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  have : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  have : F.PreservesFlat := F.preservesFlat_of_isEquivalence
  let : (ProEtale.finiteCoefficientIntrinsicComparison X A).Monoidal :=
    inferInstanceAs (V ⋙ F).Monoidal
  refine ⟨inferInstance, ?_, inferInstanceAs (V ⋙ F).PreservesFlat⟩
  intro M N U x y
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let P := ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let δ := Functor.OplaxMonoidal.δ V M N
  let η := (ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit
  let μ := Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N
  have hn := (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.naturality
    (P.map δ.hom)
  have hn' := congrArg (fun z ↦ z.app (op (X.toProEt.obj U))
    ((η.app (M ⊗ N)).hom.app (op U) (μ.app (op U) (x ⊗ₜ y)))) hn
  change ProEtale.intrinsicSection X A (V.obj M ⊗ V.obj N) (op (X.toProEt.obj U))
      (δ.hom.app (op (X.toProEt.obj U))
        ((η.app (M ⊗ N)).hom.app (op U) (μ.app (op U) (x ⊗ₜ y)))) =
    (F.map δ).val.app (op (X.toProEt.obj U))
      (ProEtale.finiteCoefficientComparisonSection X A (M ⊗ N) U
        (μ.app (op U) (x ⊗ₜ y))) at hn'
  change (Functor.OplaxMonoidal.δ F (V.obj M) (V.obj N)).val.app
    (op (X.toProEt.obj U))
    ((F.map δ).val.app (op (X.toProEt.obj U))
      (ProEtale.finiteCoefficientComparisonSection X A (M ⊗ N) U
        (μ.app (op U) (x ⊗ₜ y)))) = _
  rw [← hn', ProEtale.comparisonTensor_pure X A M N U x y]
  exact hF (V.obj M) (V.obj N) (op (X.toProEt.obj U))
    ((η.app M).hom.app (op U) x) ((η.app N).hom.app (op U) y)
end
private theorem siteChain_eq (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    [hG : (ProEtale.finiteCoefficientIntrinsicComparison X A).Monoidal]
    (hn : ProEtale.FiniteCoefficientTensorNormalization X A
      (Functor.Monoidal.μNatIso (ProEtale.finiteCoefficientIntrinsicComparison X A)).symm)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    ((ProEtale.finiteCoefficientIntrinsicComparison X A).mapCochainComplexμIso P Q).symm =
      ProEtale.finiteCoefficientIntrinsicChainTensor X A P Q := by
  let G := ProEtale.finiteCoefficientIntrinsicComparison X A
  have : PreservesColimitsOfSize.{0, 0} G := ProEtale.nu_preservesColimits X A
  apply (ProEtale.finiteCoefficientIntrinsicChainTensor_existsUnique X A P Q).choose_spec.2
  refine ⟨(Functor.Monoidal.μNatIso G).symm, hn, ?_⟩
  intro p q k h
  change G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫
      (G.mapCochainComplexμIso P Q).inv.f k =
    Functor.OplaxMonoidal.δ G (P.X p) (Q.X q) ≫
      HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor _) (.up ℤ) p q k h
  simpa only [Functor.mapCochainComplexμIso_inv,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans,
    HomologicalComplex.ιTensorObj] using
      HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
        (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ) P Q p q k h
private def coreOfConstraints {D : Type d} [Category.{h} D]
    (a r : MonoidalCategory D) (I : D)
    (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (e : @tensor D _ a ≅ @tensor D _ r)
    (hc : RingedKFlatModel.Constraints a r I ua ur e) :
    @Functor.CoreMonoidal D _ a D _ r (𝟭 D) := by
  let ta := @tensor D _ a
  let tr := @tensor D _ r
  have hl (X : D) :
      e.hom.app (a.tensorUnit, X) ≫ tr.map (X := (a.tensorUnit, X)) (Y := (r.tensorUnit, X))
        (Prod.mkHom (ua.hom ≫ ur.inv) (𝟙 X)) ≫
        (r.leftUnitor X).hom = (a.leftUnitor X).hom := by
    have hn := e.hom.naturality (Prod.mkHom ua.hom (𝟙 X))
    have hh := congrArg (fun f ↦ ta.map (X := (a.tensorUnit, X)) (Y := (I, X))
      (Prod.mkHom ua.hom (𝟙 X)) ≫ f) (hc.2.1 X)
    dsimp only [ta, tr] at hn hh ⊢
    simp only [← Category.assoc] at hh
    rw [hn] at hh
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Category.comp_id, Prod.mkHom, prod_comp, ← prod_id'] at hh
    simpa only [(@tensor D _ a).map_id, Category.id_comp, Prod.mkHom] using hh
  have hr (X : D) :
      e.hom.app (X, a.tensorUnit) ≫ tr.map (X := (X, a.tensorUnit)) (Y := (X, r.tensorUnit))
        (Prod.mkHom (𝟙 X) (ua.hom ≫ ur.inv)) ≫
        (r.rightUnitor X).hom = (a.rightUnitor X).hom := by
    have hn := e.hom.naturality (Prod.mkHom (𝟙 X) ua.hom)
    have hh := congrArg (fun f ↦ ta.map (X := (X, a.tensorUnit)) (Y := (X, I))
      (Prod.mkHom (𝟙 X) ua.hom) ≫ f) (hc.2.2 X)
    dsimp only [ta, tr] at hn hh ⊢
    simp only [← Category.assoc] at hh
    rw [hn] at hh
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Category.comp_id, Prod.mkHom, prod_comp, ← prod_id'] at hh
    simpa only [(@tensor D _ a).map_id, Category.id_comp, Prod.mkHom] using hh
  refine @Functor.CoreMonoidal.mk' D _ a D _ r (𝟭 D)
    (ur ≪≫ ua.symm)
    (fun X Y ↦ (e.app (X, Y)).symm)
    (μIso_inv_natural_left := fun f X ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @tensorHom_id D _ a, @tensorHom_id D _ r] using
        (e.hom.naturality (Prod.mkHom f (𝟙 X))).symm)
    (μIso_inv_natural_right := fun X f ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @id_tensorHom D _ a, @id_tensorHom D _ r] using
        (e.hom.naturality (Prod.mkHom (𝟙 X) f)).symm)
    (oplax_associativity := fun X Y Z ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @tensorHom_id D _ a, @tensorHom_id D _ r,
        @id_tensorHom D _ a, @id_tensorHom D _ r] using hc.1 X Y Z)
    (oplax_left_unitality := fun X ↦ by
      change (r.leftUnitor X).inv = (a.leftUnitor X).inv ≫ e.hom.app (a.tensorUnit, X) ≫
        r.whiskerRight (ua.hom ≫ ur.inv) X
      apply (cancel_mono (r.leftUnitor X).hom).1
      have hh := hl X
      simp only [tr, tensor_map, @tensorHom_id D _ r] at hh
      rw [Category.assoc, Category.assoc, hh, Iso.inv_hom_id, Iso.inv_hom_id])
    (oplax_right_unitality := fun X ↦ by
      change (r.rightUnitor X).inv = (a.rightUnitor X).inv ≫ e.hom.app (X, a.tensorUnit) ≫
        r.whiskerLeft X (ua.hom ≫ ur.inv)
      apply (cancel_mono (r.rightUnitor X).hom).1
      have hh := hr X
      simp only [tr, tensor_map, @id_tensorHom D _ r] at hh
      rw [Category.assoc, Category.assoc, hh, Iso.inv_hom_id, Iso.inv_hom_id])
private theorem targetCore
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    ∃ s : @Functor.CoreMonoidal (normalizedDVRDerived l E X n) _
      (RingedDerivedNative.monoidal.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)) _ _
      (finiteIntrinsicClosed l E X n).monoidal (𝟭 _),
    ∀ (P Q : CochainComplex (normalizedDVRModules l E X n) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
      (RingedDerivedNative.tensorIso.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) P Q (Or.inl hP)).hom ≫
        (@Functor.CoreMonoidal.μIso _ _
          (RingedDerivedNative.monoidal.{u + 1, u, u, u + 2} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X n)) _ _
          (finiteIntrinsicClosed l E X n).monoidal (𝟭 _) s
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv =
        ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) P Q hP hQ).hom := by
  have hn := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finite_tensor_coherence n
  change ∃ β : @SymmetricCategory (normalizedDVRDerived l E X n) _
      (finiteIntrinsicClosed l E X n).monoidal,
    Nonempty (RingedDerivedTensorCoherence (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n) (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicTensorModels l E X n) β) at hn
  obtain ⟨β, ⟨hc⟩⟩ := hn
  obtain ⟨e, he⟩ := RingedKFlatModel.comparison_exists.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
  have hcoh := RingedKFlatModel.comparison_constraints.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) β hc e he
  with_unfolding_all
    refine ⟨coreOfConstraints
      (RingedDerivedNative.monoidal.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n))
      (finiteIntrinsicClosed l E X n).monoidal
      (DerivedCategory.Q.obj (ringedTensorUnitComplex (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)))
      (RingedDerivedNative.unitIso.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)) hc.unitIso e hcoh, ?_⟩
  intro P Q hP hQ
  exact he P Q hP hQ
private def compCore {C : Type a} {D : Type b} {E : Type c}
    [Category.{ha} C] [Category.{hb} D] [Category.{hc} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    (F ⋙ G).CoreMonoidal := Functor.CoreMonoidal.ofOplaxMonoidal (F ⋙ G)
private def postCore {C : Type a} {D : Type b}
    [Category.{ha} C] [Category.{hb} D] [hC : MonoidalCategory C]
    (a r : MonoidalCategory D) (F : C ⥤ D)
    (m : @Functor.Monoidal C _ hC D _ a F)
    (s : @Functor.CoreMonoidal D _ a D _ r (𝟭 D)) :
    @Functor.CoreMonoidal C _ hC D _ r F :=
  @compCore C D D _ _ _ hC a r F (𝟭 D) m
    (@Functor.CoreMonoidal.toMonoidal D _ a D _ r (𝟭 D) s)
private theorem postCore_inv {C : Type a} {D : Type b}
    [Category.{ha} C] [Category.{hb} D] [MonoidalCategory C]
    (a r : MonoidalCategory D) (F : C ⥤ D)
    (m : @Functor.Monoidal C _ _ D _ a F)
    (s : @Functor.CoreMonoidal D _ a D _ r (𝟭 D)) (X Y : C) :
    ((postCore a r F m s).μIso X Y).inv =
      @Functor.OplaxMonoidal.δ C _ _ D _ a F m.toOplaxMonoidal X Y ≫
        (@Functor.CoreMonoidal.μIso D _ a D _ r (𝟭 D) s (F.obj X) (F.obj Y)).inv := by
  rfl
private theorem targetCore_cancel {D : Type b} [Category.{hb} D]
    (a r : MonoidalCategory D)
    (s : @Functor.CoreMonoidal D _ a D _ r (𝟭 D))
    {P Q R S L : D} (f : P ⟶ R) (g : Q ⟶ S)
    (x : L ≅ a.tensorObj R S) (y : L ≅ r.tensorObj R S)
    (h : x.hom ≫ (@Functor.CoreMonoidal.μIso D _ a D _ r (𝟭 D) s R S).inv = y.hom) :
    (@Functor.CoreMonoidal.μIso D _ a D _ r (𝟭 D) s P Q).inv ≫
      (@tensor D _ r).map (X := (P, Q)) (Y := (R, S)) (f, g) ≫ y.inv =
      (@tensor D _ a).map (X := (P, Q)) (Y := (R, S)) (f, g) ≫ x.inv := by
  have hn := @Functor.OplaxMonoidal.δ_natural D _ a D _ r (𝟭 D)
    (@Functor.CoreMonoidal.toOplaxMonoidal D _ a D _ r (𝟭 D) s) P R Q S f g
  change (@Functor.CoreMonoidal.μIso D _ a D _ r (𝟭 D) s P Q).inv ≫
      (@tensor D _ r).map (X := (P, Q)) (Y := (R, S)) (f, g) =
      (@tensor D _ a).map (X := (P, Q)) (Y := (R, S)) (f, g) ≫
        (@Functor.CoreMonoidal.μIso D _ a D _ r (𝟭 D) s R S).inv at hn
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  apply (cancel_epi x.hom).1
  rw [← Category.assoc, h, Iso.hom_inv_id, Iso.hom_inv_id]
private def coreTensorIso {C : Type a} {D : Type b} [Category.{ha} C] [Category.{hb} D]
    (a : MonoidalCategory C) (r : MonoidalCategory D) (F : C ⥤ D)
    (s : @Functor.CoreMonoidal C _ a D _ r F) :
    @tensor C _ a ⋙ F ≅ F.prod F ⋙ @tensor D _ r :=
  (@Functor.Monoidal.μNatIso C _ a D _ r F s.toMonoidal).symm
private theorem coreSourceTransport {C : Type a} {D : Type b}
    [Category.{ha} C] [Category.{hb} D]
    (a b : MonoidalCategory C) (r : MonoidalCategory D) (h : a = b) (F : C ⥤ D)
    (N : (c : MonoidalCategory C) →
      (@tensor C _ c ⋙ F ≅ F.prod F ⋙ @tensor D _ r) → Prop)
    (s : @Functor.CoreMonoidal C _ b D _ r F) (hs : N b (coreTensorIso b r F s)) :
    ∃ t : @Functor.CoreMonoidal C _ a D _ r F, N a (coreTensorIso a r F t) := by
  subst b
  exact ⟨s, hs⟩
private theorem etaleMonoidal_eq
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    (finiteHomEtaleClosed l E X n).monoidal =
      (inferInstance : MonoidalCategory (finiteHomEtale l E X n)) := by
  have hc := congrArg CoefficientClosedStructure.monoidal
    (eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n))
  exact hc.trans (finiteHomEtaleClosed_existsUnique (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).choose_spec.1.1
private def siteNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ)
    (a : MonoidalCategory (finiteHomEtale l E X n))
    (e : @tensor _ _ a ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor) : Prop :=
  let S : ObjectProperty (CochainComplex (normalizedDVRModules l E X n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
  let P := fun A ↦ S ((finiteHomNuComplex l E X n).obj A)
  FiniteHomNuTensorNormalizationAux
    (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
    (finiteHomNuComplex l E X n) (finiteHomNu l E X n) (finiteHomNuFactors l E X n)
    P S (fun _ h ↦ h) (finiteHomCochainTensorGeneral _)
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n))
    (@tensor _ _ a) (finiteIntrinsicClosed l E X n).tensor
    (finiteIntrinsicTensorModels l E X n).comparison
    (finiteHomEtaleTensorModel l E X n) (finiteHomNuChainTensor l E X n) e
private theorem finishCore
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ)
    (s : @Functor.CoreMonoidal _ _
      (inferInstance : MonoidalCategory (finiteHomEtale l E X n)) _ _
      (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n))
    (hs : siteNormalization l E X n _ (coreTensorIso _ _ _ s)) :
    ∃ t : @Functor.CoreMonoidal _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
        (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n),
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
        (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n) t P Q) =
        ((finiteHomNuTensor l E X n).app (P, Q)).symm := by
  obtain ⟨t, ht⟩ := coreSourceTransport (finiteHomEtaleClosed l E X n).monoidal
    (inferInstance : MonoidalCategory (finiteHomEtale l E X n))
    (finiteIntrinsicClosed l E X n).monoidal (etaleMonoidal_eq l E X n)
    (finiteHomNu l E X n) (siteNormalization l E X n) s hs
  have hn : FiniteHomNuTensorNormalization l E X n (coreTensorIso _ _ _ t) := ht
  have he := (finiteHomNuTensor_existsUnique l E X n).choose_spec.2 _ hn
  refine ⟨t, ?_⟩
  intro P Q
  apply Iso.ext
  exact congrArg (fun e ↦ e.inv.app (P, Q)) he
private theorem etaleModel_heq
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    HEq (finiteHomEtaleTensorModel l E X n P Q)
      (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  exact (finiteHomEtaleRepresentativeData_existsUnique l E X).choose_spec.1.model n P Q
set_option maxHeartbeats 1000000 in
-- Comparing the native and recorded localization instances needs a larger unification budget.
private theorem normalizedNativeCore
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    ∃ s : @Functor.CoreMonoidal _ _
      (inferInstance : MonoidalCategory (finiteHomEtale l E X n)) _ _
      (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n),
      siteNormalization l E X n _ (coreTensorIso _ _ _ s) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let G := ProEtale.finiteCoefficientIntrinsicComparison X A
  obtain ⟨m, hm, hf⟩ := ordinarySiteMonoidal X A
  let : G.Monoidal := m
  let : (ProEtale.finiteCoefficientIntrinsicComparison X A).Monoidal := m
  let : G.PreservesFlat := hf
  let : PreservesColimitsOfSize.{0, 0} G := ProEtale.nu_preservesColimits X A
  obtain ⟨d, hd⟩ := ConstantModuleDerivedProjection.exact_monoidal_normalization G m
  let native := RingedDerivedNative.monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
  let chosen := (finiteIntrinsicClosed l E X n).monoidal
  obtain ⟨t, ht⟩ := targetCore l E X n
  let s := postCore native chosen (finiteHomNu l E X n) d t
  refine ⟨s, ?_⟩
  intro P Q hx hy
  refine ⟨Functor.LaxMonoidal.μ DerivedCategory.Q P Q,
    (G.mapCochainComplexμIso P Q).symm, (etaleModel_heq l E X n P Q).symm, ?_, ?_⟩
  · have he : (G.mapCochainComplexμIso P Q).symm = finiteHomNuChainTensor l E X n P Q :=
      siteChain_eq X A hm P Q
    exact heq_of_eq he
  · let GP := (finiteHomNuComplex l E X n).obj P
    let GQ := (finiteHomNuComplex l E X n).obj Q
    have hT := targetCore_cancel native chosen t
      ((finiteHomNuFactors l E X n).hom.app P)
      ((finiteHomNuFactors l E X n).hom.app Q)
      (RingedDerivedNative.tensorIso.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) GP GQ (Or.inl hx))
      ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) GP GQ hx hy) (ht GP GQ hx hy)
    change (@Functor.CoreMonoidal.μIso _ _ _ _ _ chosen
      (finiteHomNu l E X n) s ((finiteHomEtaleQ l E X n).obj P)
        ((finiteHomEtaleQ l E X n).obj Q)).inv ≫ _ ≫ _ = _
    rw [postCore_inv, Category.assoc]
    let f := @Functor.OplaxMonoidal.δ _ _ _ _ _ native (finiteHomNu l E X n)
      d.toOplaxMonoidal ((finiteHomEtaleQ l E X n).obj P)
        ((finiteHomEtaleQ l E X n).obj Q)
    exact (congrArg (fun z ↦ f ≫ z) hT).trans
      (hd P Q (finiteHomNuKFlatReflection l E X n P hx)
        (finiteHomNuKFlatReflection l E X n Q hy))
/-- The normalized site comparison admits a core monoidal structure with its
prescribed inverse tensorator.

Source: the site-comparison paragraph of the finite-Hom proof
(blueprint: lem-coef-finite-hom-normalized-site-strong). Choose simultaneous
K-flat representatives, identify the normalized binary comparison with the
ordinary pure-tensor chain map, and descend the naturality, associativity and
unit equations through localization. The representative comparison is unique
by `finiteHomNuTensor_existsUnique`; the supplied intrinsic tensor model and
its coherence identify the descended constraints with the chosen target closed
structure. This constructs only the `CoreMonoidal` data. -/
theorem finiteHomNormalizedSiteStrong
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ)
    : ∃ s : @Functor.CoreMonoidal _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
        (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n),
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ (finiteHomEtaleClosed l E X n).monoidal _ _
        (finiteIntrinsicClosed l E X n).monoidal (finiteHomNu l E X n) s P Q) =
        ((finiteHomNuTensor l E X n).app (P, Q)).symm := by
  obtain ⟨s, hs⟩ := normalizedNativeCore l E X n
  exact finishCore l E X n s hs
end WeilConjectures
