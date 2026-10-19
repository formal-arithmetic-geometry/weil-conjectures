/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.DirectImageTensorPullbackLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Normalization of the scalar pullback mate on flat K-flat complexes

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Step 1; Stacks 03EL, 07A4, 07A6.
(blueprint: lem-sp-direct-image-tensor-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
-- Use the factorization API without unfolding the derived localization constructions.
attribute [local irreducible] Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem exactSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom.app
          (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K) := by
  have h :
      ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
          Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom.app
            (DerivedCategory.Q.obj K) ≫
          H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
          H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
          L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
              (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) := by
    have h₁ := Functor.mapDerivedCategoryCompIso_fac L H K
    have h₂ := Functor.mapDerivedCategoryCompIso_fac G L' K
    have h₃ := Functor.mapDerivedCategoryNatIso_fac s K
    apply (cancel_mono (DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K))).1
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [h₁, h₃, ← h₂]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
    have hc : DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rw [hc, Category.comp_id]
  have hc₀ : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K =
        (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact h.trans (congrArg (fun z ↦
    L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map z) hc₀)


private theorem conjugateIso_unit
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ≅ R₂) (M : C) :
    a₂.unit.app M ≫ d.inv.app (L₂.obj M) =
      a₁.unit.app M ≫ R₁.map
        (((conjugateIsoEquiv a₁ a₂).symm d).symm.hom.app M) := by
  exact unit_conjugateEquiv_symm a₂ a₁ d.inv M

namespace AlgebraicGeometry.ProEtale


variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem directImageTensorCoefficientSquare :
    (proEtaleConstantRingComparison f A).hom ≫ proEtaleConstantRingMap (T := X) φ =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) φ) ≫ (proEtaleConstantRingComparison f B).hom := by
  simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
    (proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (RingHom.ulift φ))).symm

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

private def directImageTensorOrdinaryScalarPullback :
    reductionChange Y (proEtaleConstantRingMap (T := Y) φ) ⋙ proEtaleConstantRingPullback B f ≅
      proEtaleConstantRingPullback A f ⋙ reductionChange X
        (proEtaleConstantRingMap (T := X) φ) :=
  ((conjugateIsoEquiv
    ((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).comp
      (proEtaleConstantRingAdjunction B f))
    ((proEtaleConstantRingAdjunction A f).comp
      (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)))).symm
    (proEtaleRingRestrictionDirectImage f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f))).symm

private def directImageTensorOrdinaryComparison :
    reductionChange Y (proEtaleConstantRingMap (T := Y) φ) ⋙
      proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ) ⋙
      proEtaleConstantRingPullback A f ⟶
    proEtaleConstantRingPullback A f ⋙
      reductionChange X (proEtaleConstantRingMap (T := X) φ) ⋙
      proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ) :=
  Functor.whiskerLeft (reductionChange Y (proEtaleConstantRingMap (T := Y) φ))
    (proEtaleRingRestrictionPullbackInv f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f)) ≫
    Functor.whiskerRight (directImageTensorOrdinaryScalarPullback φ f).hom
      (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ))

attribute [local irreducible] directImageTensorOrdinaryComparison

/-- The termwise ordinary comparison; naturality makes it a chain map.
Source: Stacks 03EL and 07A6; blueprint direct-image proof, Step 1
(blueprint: lem-sp-direct-image-tensor-pullback-normalization). -/
private def directImageTensorComparisonComplex
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ) :
    ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
      (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
        (.up ℤ)).obj ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ⟶
      ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
        (.up ℤ)).obj ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
          (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (NatTrans.mapHomologicalComplex (directImageTensorOrdinaryComparison φ f) (.up ℤ)).app P

private theorem directImageTensorOrdinaryScalarPullback_unit
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (((proEtaleConstantRingAdjunction A f).comp
      (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))).unit.app M) ≫
      (proEtaleRingRestrictionDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (directImageTensorCoefficientSquare φ f)).inv.app
          (((proEtaleConstantRingPullback A f) ⋙
            reductionChange X (proEtaleConstantRingMap (T := X) φ)).obj M) =
    (((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).comp
      (proEtaleConstantRingAdjunction B f)).unit.app M) ≫
      ((proEtaleRingModuleDirectImage f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)) ⋙
          proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).map
            ((directImageTensorOrdinaryScalarPullback φ f).hom.app M) := by
  exact conjugateIso_unit
    ((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).comp
      (proEtaleConstantRingAdjunction B f))
    ((proEtaleConstantRingAdjunction A f).comp
      (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))) _ M

-- Subsequent calculations use the unit API rather than unfolding the composite mate.
attribute [local irreducible] directImageTensorOrdinaryScalarPullback

private theorem ordinaryMate_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ C) (R : C ⥤ A) (L' : B ⥤ D) (R' : D ⥤ B)
    (S : B ⥤ A) (T : D ⥤ C) (a : L ⊣ R) (a' : L' ⊣ R')
    (d : R' ⋙ S ⟶ T ⋙ R) (M : B) (N : D) (t : L'.obj M ⟶ N) :
    a.homEquiv _ _
      ((L.map (S.map (a'.unit.app M)) ≫ L.map (d.app (L'.obj M)) ≫
        a.counit.app _) ≫ T.map t) =
      S.map (a'.homEquiv _ _ t) ≫ d.app N := by
  have h : L.map (S.map (a'.unit.app M)) ≫ L.map (d.app (L'.obj M)) ≫
      a.counit.app _ = (a.homEquiv _ _).symm
        (S.map (a'.unit.app M) ≫ d.app (L'.obj M)) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [h, Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  rw [Category.assoc]
  have hd := d.naturality t
  dsimp only [Functor.comp_map] at hd
  rw [← hd, ← Category.assoc, ← S.map_comp, Adjunction.homEquiv_unit]

private theorem directImageTensorOrdinaryComparison_transpose
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    ((proEtaleConstantRingAdjunction A f).homEquiv _ _)
      ((directImageTensorOrdinaryComparison φ f).app M) =
      (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).map
        (((proEtaleConstantRingAdjunction B f).homEquiv _ _)
          ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)) ≫
        (proEtaleRingRestrictionDirectImage f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (directImageTensorCoefficientSquare φ f)).hom.app
            ((reductionChange X (proEtaleConstantRingMap (T := X) φ)).obj
              ((proEtaleConstantRingPullback A f).obj M)) := by
  simpa only [directImageTensorOrdinaryComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, proEtaleRingRestrictionPullbackInv,
    proEtaleRingRestrictionPullbackApp, proEtaleConstantRingPullback,
    proEtaleConstantRingPushforward, proEtaleConstantRingAdjunction,
    Functor.comp_obj, Functor.id_obj, Category.assoc] using ordinaryMate_transpose
    (proEtaleConstantRingPullback A f) (proEtaleConstantRingPushforward A f)
    (proEtaleConstantRingPullback B f) (proEtaleConstantRingPushforward B f)
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ))
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ))
    (proEtaleConstantRingAdjunction A f) (proEtaleConstantRingAdjunction B f)
    (proEtaleRingRestrictionDirectImage f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f)).hom
    ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj M) _
    ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)


set_option maxHeartbeats 800000 in
-- The mate involves four specified adjunction structures.
private theorem directImageTensorOrdinaryScalarPullback_unit_square
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).unit.app M ≫
      ((proEtaleConstantRingAdjunction A f).homEquiv _ _)
        ((directImageTensorOrdinaryComparison φ f).app M) =
    (proEtaleConstantRingAdjunction A f).unit.app M ≫
      (proEtaleConstantRingPushforward A f).map
        ((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app
          ((proEtaleConstantRingPullback A f).obj M)) := by
  erw [directImageTensorOrdinaryComparison_transpose φ f M]
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f)
  have hu := directImageTensorOrdinaryScalarPullback_unit φ f M
  have hu' := (Iso.comp_inv_eq (d.app _)).mp hu
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map,
    Category.assoc] at hu'
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  exact hu'.symm

set_option maxHeartbeats 800000 in
-- Elaborate the independent ring and module universe transports.
private theorem tensorSection_smul
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    reductionTensorSection T φ M U s x =
      s • reductionTensorSection T φ M U 1 x := by
  let e := eqToHom ((completedAdicChangeData T φ).choose_spec.choose M).symm
  let q := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom _ (φ.hom.app U).hom
  have ht : (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
      s • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := R.obj.obj U) s (1 : S.obj.obj U) x).symm
  change (e.val.app U) (q (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • (e.val.app U) (q ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun z ↦ (e.val.app U) (q z)) ht).trans
    ((congrArg (fun z ↦ (e.val.app U) z)
      (q.hom.map_smulₛₗ s
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))).trans
          ((e.val.app U).hom.map_smul s _))

private theorem scalarUnit_section
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x =
      reductionTensorSection T φ M U 1 x := by
  exact (Classical.choose_spec (pbcScalarAdjunction_exists φ).exists) M U x



set_option maxHeartbeats 800000 in
-- The ordinary mate retains four adjunction structures and their scalar actions.
private theorem directImageTensorOrdinaryScalarPullback_section_one
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEt) (x : M.val.obj (Opposite.op U)) :
    (((proEtaleConstantRingAdjunction B f).homEquiv _ _)
      ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app (Opposite.op U)
        (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
          (Opposite.op U) 1 x) =
      reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U)) 1
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) := by
  have h := directImageTensorOrdinaryScalarPullback_unit_square φ f M
  have ht := directImageTensorOrdinaryComparison_transpose φ f M
  simp only [proEtaleRingExtensionAdjunction, proEtaleRingExtension, Functor.comp_obj] at h ht
  erw [ht] at h
  have hx := congrArg (fun z ↦ z.val.app (Opposite.op U) x) h
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f)
  have hd := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f))).1
  change (d.hom.app _).val.app (Opposite.op U)
    (((proEtaleConstantRingAdjunction B f).homEquiv _ _
      ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app (Opposite.op U)
        (((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).unit.app
          M).val.app (Opposite.op U) x)) =
    ((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app
      ((proEtaleConstantRingPullback A f).obj M)).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U))
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) at hx
  rw [show (d.hom.app _).val.app (Opposite.op U) _ = _ from hd _ _ _] at hx
  have hy := scalarUnit_section Y (proEtaleConstantRingMap (T := Y) φ) M
    (Opposite.op U) x
  have hxunit := scalarUnit_section X (proEtaleConstantRingMap (T := X) φ)
    ((proEtaleConstantRingPullback A f).obj M)
    (Opposite.op ((proEtaleBaseChange f).obj U))
    (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x)
  exact (congrArg (fun z ↦
    (((proEtaleConstantRingAdjunction B f).homEquiv _ _)
      ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app
        (Opposite.op U) z) hy.symm).trans
        (hx.trans hxunit)


set_option maxHeartbeats 800000 in
-- Keep the scalar actions of direct image explicit in the section calculation.
private theorem directImageTensorOrdinaryScalarPullback_section
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEt) (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op U))
    (x : M.val.obj (Opposite.op U)) :
    (((proEtaleConstantRingAdjunction B f).homEquiv _ _)
      ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app (Opposite.op U)
        (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
          (Opposite.op U) s x) =
      reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U))
        (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
          (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
            (Opposite.op U)) s)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) := by
  let g := (((proEtaleConstantRingAdjunction B f).homEquiv _ _)
    ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app (Opposite.op U)
  erw [tensorSection_smul]
  have hg := g.hom.map_smul s
    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
      (Opposite.op U) 1 x)
  change g (s • _) = _ at hg
  erw [hg]
  change (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
    (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
      (Opposite.op U)) s) •
      (show ((reductionChange X (proEtaleConstantRingMap (T := X) φ)).obj
        ((proEtaleConstantRingPullback A f).obj M)).val.obj
          (Opposite.op ((proEtaleBaseChange f).obj U)) from g _) = _
  erw [show g _ = _ from directImageTensorOrdinaryScalarPullback_section_one φ f M U x]
  exact (tensorSection_smul X (proEtaleConstantRingMap (T := X) φ)
    ((proEtaleConstantRingPullback A f).obj M)
    (Opposite.op ((proEtaleBaseChange f).obj U)) _ _).symm

set_option maxHeartbeats 800000 in
-- Relate the two ordinary transposes on the unchanged underlying sections.
/-- The ordinary comparison sends the pullback unit of s tensor x to
c_B(s) tensor the pullback unit of x.

Proof: conjugacy of the composite adjunctions gives the unit square. Transpose
under the A-pullback adjunction and evaluate on sections. The direct-image
restriction comparison is identity on these sections. The scalar unit is 1 tensor x,
so the equation holds at s=1. B-linearity gives the equation for arbitrary s.
Transposing back gives the displayed formula. This works for all modules;
no flatness or K-flatness is required.
Source: Stacks 03EL and 07A6; blueprint direct-image proof, Step 1
(blueprint: lem-sp-direct-image-tensor-pullback-normalization). -/
private theorem directImageTensorOrdinaryComparison_section
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEt) (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op U))
    (x : M.val.obj (Opposite.op U)) :
    ((directImageTensorOrdinaryComparison φ f).app M).val.app
      (Opposite.op ((proEtaleBaseChange f).obj U))
        (((proEtaleConstantRingAdjunction A f).unit.app
          ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ) ⋙
            proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).obj M)).val.app
              (Opposite.op U)
              (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
                (Opposite.op U) s x)) =
      reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
        ((proEtaleConstantRingPullback A f).obj M)
        (Opposite.op ((proEtaleBaseChange f).obj U))
        (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
          (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
            (Opposite.op U)) s)
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op U) x) := by
  have h := directImageTensorOrdinaryComparison_transpose φ f M
  have hx := congrArg (fun z ↦ z.val.app (Opposite.op U)
    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
      (Opposite.op U) s x)) h
  rw [Adjunction.homEquiv_unit] at hx
  have hd := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f))).1
  change ((directImageTensorOrdinaryComparison φ f).app M).val.app
      (Opposite.op ((proEtaleBaseChange f).obj U))
        (((proEtaleConstantRingAdjunction A f).unit.app
          ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ) ⋙
            proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).obj M)).val.app
              (Opposite.op U)
              (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
                (Opposite.op U) s x)) =
      ((proEtaleRingRestrictionDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (directImageTensorCoefficientSquare φ f)).hom.app
          ((reductionChange X (proEtaleConstantRingMap (T := X) φ)).obj
            ((proEtaleConstantRingPullback A f).obj M))).val.app (Opposite.op U)
              ((((proEtaleConstantRingAdjunction B f).homEquiv _ _)
                ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app
                  (Opposite.op U)
                  (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
                    (Opposite.op U) s x)) at hx
  rw [show ((proEtaleRingRestrictionDirectImage f
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
        (directImageTensorCoefficientSquare φ f)).hom.app
          ((reductionChange X (proEtaleConstantRingMap (T := X) φ)).obj
            ((proEtaleConstantRingPullback A f).obj M))).val.app (Opposite.op U)
              ((((proEtaleConstantRingAdjunction B f).homEquiv _ _)
                ((directImageTensorOrdinaryScalarPullback φ f).hom.app M)).val.app
                  (Opposite.op U)
                  (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M
                    (Opposite.op U) s x)) = _ from hd _ _ _] at hx
  exact hx.trans (directImageTensorOrdinaryScalarPullback_section φ f M U s x)



private theorem ordinaryScalar_unit
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleConstantRingPullback A f).map
        ((proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).unit.app M) ≫
      (directImageTensorOrdinaryComparison φ f).app M =
    (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app
      ((proEtaleConstantRingPullback A f).obj M) := by
  apply ((proEtaleConstantRingAdjunction A f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [directImageTensorOrdinaryScalarPullback_unit_square]
  rfl

private def ordinaryScalarComplex
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ) :
    ((proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ)).obj
        ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P) ⟶
      (reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
        (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (directImageTensorOrdinaryScalarPullback φ f).hom
    (.up ℤ)).app P


private def ordinaryRestrictionComplex
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y B)) ℤ) :
    ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
      (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
        (.up ℤ)).obj K) ⟶
    ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
      (.up ℤ)).obj (((proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f)) (.up ℤ)).app K

private theorem restrictionFactors
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y B)) ℤ) :
    (proEtaleRingRestrictionDerivedPullback f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f)).inv.app (DerivedCategory.Q.obj K) ≫
      (scalarRestriction φ X).map
        ((proEtaleConstantRingPullback B f).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := X) φ)).mapDerivedCategoryFactors.hom.app
        (((proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ)).obj K) =
    (constantPullback (A := A) f).map
      ((proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := Y) φ)).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
          (.up ℤ)).obj K) ≫ DerivedCategory.Q.map (ordinaryRestrictionComplex φ f K) := by
  have := proEtaleRingRestrictionPullbackInv_isIso f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f)
  let b := asIso (proEtaleRingRestrictionPullbackInv f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (directImageTensorCoefficientSquare φ f))
  have h := exactSquare_factors (proEtaleConstantRingPullback B f)
    (proEtaleConstantRingPullback A f)
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ))
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)) b K
  have hb : (proEtaleRingRestrictionDerivedPullback f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f)).inv =
    ((Functor.mapDerivedCategoryCompIso
      (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ))
      (proEtaleConstantRingPullback A f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso b ≪≫
      Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback B f)
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ))).hom := by
    simp only [proEtaleRingRestrictionDerivedPullback, b, Iso.trans_inv,
      Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
      ← Functor.mapDerivedCategoryNatIso_symm]
    rfl
  rw [hb]
  simpa only [ordinaryRestrictionComplex, b, asIso_hom, scalarRestriction,
    constantPullback, proEtaleRingDerivedPullback, proEtaleConstantRingPullback] using h

private theorem scalarUnit_all
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)).unit.app
        (DerivedCategory.Q.obj P) ≫
      (scalarRestriction φ T).map (scalarExtensionFunctorCounit φ T P) ≫
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := T) φ)).mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) φ)).obj P) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)).unit
        (.up ℤ)).app P) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hr : ∃ (K : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
      (q : K ⟶ P), CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := proEtaleConstantRing T A) K ∧ QuasiIso q := by
    obtain ⟨K, q, hk, _, hq, _⟩ := 
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (C := T.ProEt) (J := ProEt.topology T) (R := proEtaleConstantRing T A) P
    exact ⟨K, q, hk, hq⟩
  obtain ⟨K, q, hK, hq⟩ := hr
  let : QuasiIso q := hq
  have hunit := (Classical.choose_spec (pbcDerivedScalarAdjunction_exists
    (proEtaleConstantRingMap (T := T) φ)).exists) K hK
  apply (cancel_epi (DerivedCategory.Q.map q)).1
  have hu := (proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) φ)).unit.naturality (DerivedCategory.Q.map q)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [scalarExtensionFunctor_map φ T q]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hr := (proEtaleRingRestrictScalars
    (proEtaleConstantRingMap (T := T) φ)).mapDerivedCategoryFactors.hom.naturality
      ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) φ)).map q)
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  rw [← Category.assoc] at hunit
  rw [← Category.assoc, ← Category.assoc]
  erw [hunit]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  exact ((NatTrans.mapHomologicalComplex
    (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)).unit
      (.up ℤ)).naturality q).symm

/-- The concrete scalar-pullback mate has the balanced pure-tensor formula and its
localization square on every flat-term K-flat representative.
Source: blueprint direct-image proof, Step 1 (normalization), expanded in
lem-sp-direct-image-change-ring-transpose, Step 2; Stacks 03EL, 07A4 and 07A6.
(blueprint: lem-sp-direct-image-tensor-pullback-normalization).

Proof: take the conjugate of the ordinary restriction/direct-image comparison
under the composite scalar and pullback adjunctions. Follow the ordinary
restriction/pullback comparison by the restriction of this conjugate. Its composite
unit equation, evaluated on sections, gives the formula on 1 tensor x. B-linearity
gives the formula on s tensor x, and naturality makes the degreewise maps a chain map.
The normalized derived scalar-unit equation extends from K-flat complexes to every
complex: choose a K-flat resolution, use naturality of the unit, universal counit
and exact restriction factorization, and cancel the localized quasi-isomorphism.
The exact-functor composition and natural-isomorphism factorization lemmas identify
the localized ordinary restriction/pullback square with the specified derived square.
Apply the generic normalized-mate transport theorem with these factorizations and
the ordinary unit equation. Its resulting square is the asserted localization square.
The construction and square work for every complex; in particular they hold for
the flat-term K-flat representatives in the statement. No flatness of B over A,
boundedness, or preservation of K-flatness under pullback is needed. -/
theorem directImageChangeRing_tensorNormalization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
  ∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing Y A) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
    ∃ t : ((proEtaleConstantRingPullback A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y)
            φ)).obj P)) ⟶
        ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)),
      (∀ (i : ℤ) (U : Y.ProEt) (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op U))
        (x : (P.X i).val.obj (Opposite.op U)),
        (t.f i).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleConstantRingAdjunction A f).unit.app
              ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).obj
                ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj (P.X i)))).val.app
                (Opposite.op U)
                (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) (P.X i) (Opposite.op
                  U) s x)) =
          reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
            ((proEtaleConstantRingPullback A f).obj (P.X i))
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
              (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
                (Opposite.op U)) s)
            (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
              (Opposite.op U) x)) ∧
      (constantPullback (A := A) f).map
          ((scalarRestriction φ Y).map (scalarExtensionFunctorCounit φ Y P) ≫
            (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y)
              φ)).mapDerivedCategoryFactors.hom.app ((reductionChangeComplex Y
              (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
        (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y)
            φ)).obj P)) ≫
        DerivedCategory.Q.map t =
      ((proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (by
            simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
              (proEtaleConstantInverseImageMap_naturality f
                (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)).inv.app
            ((scalarExtensionFunctor φ Y).obj (DerivedCategory.Q.obj P)) ≫
          (scalarRestriction φ X).map
            ((tensorPullbackIso φ f).hom.app (DerivedCategory.Q.obj P))) ≫
        (scalarRestriction φ X).map
          ((scalarExtensionFunctor φ X).map ((proEtaleConstantRingPullback A
            f).mapDerivedCategoryFactors.hom.app P) ≫
            scalarExtensionFunctorCounit φ X (((proEtaleConstantRingPullback A
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X)
          φ)).mapDerivedCategoryFactors.hom.app ((reductionChangeComplex X (proEtaleConstantRingMap
          (T := X) φ)).obj (((proEtaleConstantRingPullback A f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  intro P _hP _hflat
  let t := directImageTensorComparisonComplex φ f P
  refine ⟨t, ?_, ?_⟩
  · intro i U s x
    exact directImageTensorOrdinaryComparison_section φ f (P.X i) U s x
  · let L := (proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)
    let R := (proEtaleRingRestrictScalars
      (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex (.up ℤ)
    let H := (proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ)
    let S := (proEtaleRingRestrictScalars
      (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex (.up ℤ)
    let E := reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)
    let F := reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)
    let a := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)
    let a' := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)
    let bd := (proEtaleRingRestrictionDerivedPullback f
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (directImageTensorCoefficientSquare φ f)).inv
    let u := (NatTrans.mapHomologicalComplex
      (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)).unit
      (.up ℤ)).app P
    let v := (NatTrans.mapHomologicalComplex
      (proEtaleRingExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)).unit
      (.up ℤ)).app (L.obj P)
    have hg : L.map u ≫ ordinaryRestrictionComplex φ f (E.obj P) ≫
        S.map (ordinaryScalarComplex φ f P) = v := by
      apply HomologicalComplex.hom_ext
      intro i
      dsimp only [L, S, E, u, v, reductionChangeComplex, ordinaryRestrictionComplex,
        ordinaryScalarComplex, Functor.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
        HomologicalComplex.comp_f]
      simpa only [directImageTensorOrdinaryComparison, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
        using ordinaryScalar_unit φ f (P.X i)
    have hθ : (tensorPullbackIso φ f).inv =
        ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ bd)).natTrans := rfl
    have hh := directImageChangeRing_tensorNormalization_localization
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q L R H S
      (constantPullback (A := A) f) (scalarRestriction φ Y)
      (constantPullback (A := B) f) (scalarRestriction φ X)
      (scalarExtensionFunctor φ Y) (scalarExtensionFunctor φ X) a a'
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := Y) φ)).mapDerivedCategoryFactors
      (proEtaleConstantRingPullback B f).mapDerivedCategoryFactors
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := X) φ)).mapDerivedCategoryFactors
      (ordinaryRestrictionComplex φ f) bd P (E.obj P) (F.obj (L.obj P)) u v
      (scalarExtensionFunctorCounit φ Y P)
      (scalarExtensionFunctorCounit φ X (L.obj P))
      (scalarUnit_all φ Y P) (scalarUnit_all φ X (L.obj P))
      (restrictionFactors φ f (E.obj P))
      (ordinaryScalarComplex φ f P) hg (tensorPullbackIso φ f) hθ
    have ht : ordinaryRestrictionComplex φ f (E.obj P) ≫
        S.map (ordinaryScalarComplex φ f P) = t := by
      apply HomologicalComplex.hom_ext
      intro i
      dsimp only [S, E, t, reductionChangeComplex, ordinaryRestrictionComplex,
        ordinaryScalarComplex, directImageTensorComparisonComplex, Functor.mapHomologicalComplex,
        NatTrans.mapHomologicalComplex, HomologicalComplex.comp_f]
      simp only [directImageTensorOrdinaryComparison, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [ht] at hh
    simpa only [Functor.map_comp, Category.assoc] using hh

end AlgebraicGeometry.ProEtale

