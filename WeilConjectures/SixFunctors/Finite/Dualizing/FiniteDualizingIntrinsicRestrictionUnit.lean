/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! Intrinsic identity coherence for finite dualizing restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] finiteDualizingIntrinsicRes
  finiteDualizingIntrinsicRingMap sfIntrinsicDerivedEquivalence

private theorem scalarUnit_surjective (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : Y.ProEtᵒᵖ) :
    Function.Surjective (sfIntrinsicRealizationUnit Y A M W) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap Y A
  let N := (ProEtale.finiteCoefficientModulePresheaf Y.ProEt
    (ULift.{u + 1, u} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app N
  have : IsIso η := by
    dsimp only [η, α, N]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj
        M).property
  have : IsIso (η.app W) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ W).map η))
  exact (ConcreteCategory.bijective_of_isIso (η.app W)).surjective

private theorem scalarUnit_naturality (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : Y.ProEtᵒᵖ) (x : M.obj.obj W) :
    (((sfIntrinsicModuleEquivalence Y A).functor.map f).val.app W)
        (sfIntrinsicRealizationUnit Y A M W x) =
      sfIntrinsicRealizationUnit Y A N W (f.hom.app W x) := by
  exact (ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app W)
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf Y.ProEt
            (ULift.{u + 1, u} A)).map f.hom))) x).symm

private theorem intrinsicRingMap_id (Y : Scheme.{u})
    (A : Type u) [CommRing A] (φ : A →+* A) (hφ : φ = RingHom.id A) :
    finiteDualizingIntrinsicRingMap Y φ = 𝟙 _ := by
  subst φ
  have h : CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (RingHom.id A)) =
      𝟙 (CommRingCat.of (ULift.{u + 1, u} A)) := rfl
  simp only [finiteDualizingIntrinsicRingMap, h, CategoryTheory.Functor.map_id]

private theorem restrictionId_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{u + 1} R) (W : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars.{u + 1} f).obj M).val.obj W) :
    ((eqToIso (congrArg (fun g ↦ SheafOfModules.restrictScalars.{u + 1} g) hf)).hom.app
      M).val.app W x = x := by
  subst f
  rfl

private theorem ordinaryRestriction_unit (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] (φ : A →+* A) (hφ : φ = RingHom.id A)
    (hp : finiteDualizingIntrinsicRes Y φ = 𝟭 _)
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    ((finiteDualizingRestriction_existsUnique Y φ).choose).hom.app M ≫
      (sfIntrinsicModuleEquivalence Y A).functor.map
        ((ProEtale.normalizedOriginRestrictionUnit (ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1} φ) (by subst φ; rfl)).hom.app M) =
      (eqToIso hp).hom.app ((sfIntrinsicModuleEquivalence Y A).functor.obj M) := by
  ext W x
  obtain ⟨x, rfl⟩ := scalarUnit_surjective Y A M W x
  change (((sfIntrinsicModuleEquivalence Y A).functor.map _).val.app W)
      ((((finiteDualizingRestriction_existsUnique Y φ).choose).hom.app M).val.app W
        (sfIntrinsicRealizationUnit Y A M W x)) = _
  rw [eq_of_heq ((finiteDualizingRestriction_existsUnique Y φ).choose_spec.1 M W x),
    scalarUnit_naturality]
  exact (restrictionId_apply (finiteDualizingIntrinsicRingMap Y φ)
    (intrinsicRingMap_id Y A φ hφ) ((sfIntrinsicModuleEquivalence Y A).functor.obj M)
      W (sfIntrinsicRealizationUnit Y A M W x)).symm

private theorem derivedRestriction_unit (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] (φ : A →+* A) (hφ : φ = RingHom.id A)
    (U : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A))
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (hU : U = finiteDualizingIntrinsicRes Y φ) (hp : U = 𝟭 _)
    (e : (sfIntrinsicDerivedEquivalence Y A).functor ⋙ U.mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor)
    (he : HEq e (finiteDualizingGenericDerivedRestriction Y φ))
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    e.inv.app K ≫
        (Functor.mapDerivedCategoryNatIso (eqToIso hp) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app
            ((sfIntrinsicDerivedEquivalence Y A).functor.obj K) =
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit (ProEt.topology Y)
            (RingHom.ulift.{u + 1, u + 1} φ) (by subst φ; rfl)) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K) := by
  subst U
  have he' := eq_of_heq he
  subst e
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_id
    (finiteDualizingRestriction_existsUnique Y φ).choose
    (ProEtale.normalizedOriginRestrictionUnit (ProEt.topology Y)
      (RingHom.ulift.{u + 1, u + 1} φ) (by subst φ; rfl))
    (eqToIso hp) (ordinaryRestriction_unit Y A φ hφ hp) K
  change (finiteDualizingGenericDerivedRestriction Y φ).hom.app K ≫ _ = _ at hd
  apply (cancel_epi ((finiteDualizingGenericDerivedRestriction Y φ).hom.app K)).mp
  rw [Iso.hom_inv_id_app_assoc]
  exact hd.symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

/-- The intrinsic realization restriction comparison is normalized at the identity.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
identity normalization of the intrinsic comparison.
(blueprint: lem-coef-dualizing-realization-restriction-unit-intrinsic)

The identity quotient is identified with the identity ring map.  The ordinary
section-normalized comparison is transported through exact localization; its
inverse followed by the canonical identity maps on both derived sites agrees
with the identity-normalized comparison on the pro-etale site. -/
theorem finiteDualizingIntrinsicRestriction_unit (n : ℕ) :
    (finiteDualizingIntrinsicRestriction l E X (le_refl n)).symm ≪≫
        Functor.isoWhiskerLeft
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor
          (normalizedDVRResUnit l E X n) ≪≫
        Functor.rightUnitor _ =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso
            (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology X)
              (finiteDualizingQuotient l E (le_refl n))
              (by rw [finiteDualizingQuotient_id l E n])) ≪≫
            Functor.mapDerivedCategoryIdIso _)
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor ≪≫
        Functor.leftUnitor _ := by
  have hφ : finiteDualizingQuotientBase l E (le_refl n) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    exact DFunLike.congr_fun Ideal.Quotient.factor_eq x
  let hp : normalizedDVRModuleRes l E X (le_refl n) = 𝟭 _ :=
    congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f)
      ((integralCoefficientSheafSystem l E X).map_id (op n))
  have := normalizedDVRModuleRes_limits l E X (le_refl n)
  have := normalizedDVRModuleRes_colimits l E X (le_refl n)
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app]
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id]
  exact derivedRestriction_unit X (Padic.coefficientExtensionRing l E (n + 1))
    (finiteDualizingQuotientBase l E (le_refl n)) hφ
    (normalizedDVRModuleRes l E X (le_refl n))
    (finiteDualizingRestriction_eq l E X (le_refl n)) hp
    (finiteDualizingIntrinsicRestriction l E X (le_refl n))
    (finiteDualizingIntrinsicRestriction_existsUnique l E X (le_refl n)).choose_spec.1 K

end WeilConjectures
