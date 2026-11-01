/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteEncoding.IntegralFiniteEncoding
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalarRealization
public import WeilConjectures.AlgebraicGeometry.IntegralSmallPerfect.IntegralSmallPerfectTower
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteEncodedPresentation
import all WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized finite coefficient comparisons

Source: Stacks Tags 03CY and 093J; integral local structure, proof step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open CategoryTheory.MonoidalCategory
open FiniteDiscreteOrdinary

-- Keep the cancellation abstract so elaboration does not unfold large sheaf constructions.
private def mapModComapCancelIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
    (P : C₀ ⥤ C₁) (F : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [P.LaxMonoidal] [F.LaxMonoidal] [H.LaxMonoidal]
    (α : P ⋙ F ≅ H) [NatTrans.IsMonoidal α.hom]
    (R : C₀) [MonObj R] (B : C₁) [MonObj B]
    (φ : P.obj R ⟶ B) [IsMonHom φ] [IsIso φ]
    (κ : H.obj R ⟶ F.obj B) [IsMonHom κ]
    (hs : κ ≫ F.map (inv φ) ≫ α.hom.app R = 𝟙 (H.obj R)) :
    P.mapMod R ⋙ Mod.comap (inv φ) ⋙ F.mapMod B ⋙ Mod.comap κ ≅ H.mapMod R := by
  let i₁ := Functor.isoWhiskerRight (F.mapModComapIso (inv φ)) (Mod.comap κ)
  let i₂ := Functor.isoWhiskerRight (Functor.mapModCompIso P F α.hom R)
    (Mod.comap (F.map (inv φ)) ⋙ Mod.comap κ)
  let i₃ := (Mod.comapComp κ (F.map (inv φ))).symm
  let i₄ := (Mod.comapComp (κ ≫ F.map (inv φ)) (P.compAlgHom F α.hom R)).symm
  exact Functor.isoWhiskerLeft (P.mapMod R) i₁ ≪≫ i₂ ≪≫
    Functor.isoWhiskerLeft (H.mapMod R ⋙ Mod.comap (P.compAlgHom F α.hom R)) i₃ ≪≫
    Functor.isoWhiskerLeft (H.mapMod R) i₄ ≪≫
    Functor.isoWhiskerLeft (H.mapMod R)
      (Mod.comapCongr (by simpa only [Category.assoc] using hs) ≪≫ Mod.comapId _) ≪≫
    Functor.rightUnitor _

section Comparisons
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A] (X : Scheme.{u})

attribute [local instance] canonicalAbelianMap_isMonHom

private local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

private theorem finiteScalarToContinuous_isIso :
    IsIso (FiniteConstantModel.scalarToContinuous A) := by
  let J := coherentTopology Profinite.{u}
  let φ := FiniteConstantModel.constantFunctions A
  let : Presheaf.IsLocallyInjective J φ := pointConstants_locallyInjective A
  let : Presheaf.IsLocallySurjective J φ := pointConstants_locallySurjective A
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff _).mp hφ
  unfold FiniteConstantModel.scalarToContinuous
  rw [Adjunction.homEquiv_counit]
  infer_instance

private def modelConstantInternalIso :
    FiniteConstantModel.modelFunctor A X ⋙ Mod.comap (canonicalAbelianMap A X) ≅
      FiniteConstantModel.scalarModules A ⋙
        (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod
          (AddCommGrpCat.of (ULift.{u + 1} A)) := by
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let F := upperStarFromPoint X
  let C := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let R := AddCommGrpCat.of (ULift.{u + 1} A)
  let φ := FiniteConstantModel.scalarToContinuous A
  let κ := canonicalAbelianMap A X
  let α := constantSchemeIso X
  letI : NatTrans.IsMonoidal α.hom := inferInstanceAs
    (NatTrans.IsMonoidal (constantSchemeIso X).hom)
  letI : NatTrans.IsMonoidal α.symm.hom := inferInstanceAs
    (NatTrans.IsMonoidal (constantSchemeIso X).inv)
  letI : IsIso φ := finiteScalarToContinuous_isIso A
  have hs : κ ≫ F.map (inv φ) ≫ α.inv.app R = 𝟙 (C.obj R) := by
    change (α.hom.app R ≫ F.map φ) ≫ F.map (inv φ) ≫ α.inv.app R = _
    simp [C]
  let i := Functor.isoWhiskerLeft (P.mapMod R)
    (Functor.isoWhiskerRight (Mod.extendScalarsIsoComapInv φ)
      (F.mapMod (coefficient A) ⋙ Mod.comap κ)) ≪≫
    mapModComapCancelIso P F C α.symm R (coefficient A) φ κ hs
  exact Functor.isoWhiskerLeft (FiniteConstantModel.scalarModules A) i

private def normalizedInternalIso (e : Encoding A X) :
    e.ordinary.functor ⋙ e.fixed.functor ≅ constantInternalEncoding A X := by
  rw [e.ordinary_functor, e.fixed_functor]
  exact NatIso.ofComponents (encoding_constantInternal_iso A X e)
    (by intro M N f; ext U m; rfl)

private def constantInternalPresheaves :
    Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A)) ⥤
      Mod (X.ProEtᵒᵖ ⥤ Ab.{u + 1})
        (ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) (ULift.{u + 1} A)) where
  obj := constantPresheafModule A X
  map {M N} f := Mod.homMk
    { app := fun _ ↦ f.hom
      naturality := by
        intro U V g
        change (𝟙 M.X) ≫ f.hom = f.hom ≫ (𝟙 N.X)
        simp only [Category.id_comp, Category.comp_id] }
    (by
      apply NatTrans.ext
      funext U
      exact IsModHom.smul_hom (A := AddCommGrpCat.of (ULift.{u + 1} A)) (f := f.hom))

private def constantBridgeIso :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙ constantBridge A X ≅
      constantInternalPresheaves A X ⋙
        (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod
          (ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) (ULift.{u + 1} A)) :=
  NatIso.ofComponents (constantBridgeSheafifyIso A X) (by
    intro M N f
    apply Mod.hom_ext
    change (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map f.hom ≫ 𝟙 _ =
      𝟙 _ ≫ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map f.hom
    simp only [Category.comp_id, Category.id_comp])

private def scalarModulesIso :
    FiniteConstantModel.scalarModules A ⋙ internalToModule (ULift.{u + 1} A) ≅
      ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom :=
  NatIso.ofComponents (fun M ↦ ModuleCat.isoMk (Iso.refl _) (fun _ ↦ rfl))
    (by intro M N f; ext m; rfl)

private def constantInternalFixedIso :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙ constantBridge A X ⋙
        ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X)
          (ULift.{u + 1} A) (internalToModule (ULift.{u + 1} A)) rfl ≅
      internalToModule (ULift.{u + 1} A) ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  let J := Scheme.ProEt.topology X
  let B := ULift.{u + 1} A
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J B (internalToModule B) rfl
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt)
    B (internalToModule B)
  let i : constantInternalPresheaves A X ⋙ P ≅
      internalToModule B ⋙ Functor.const X.ProEtᵒᵖ :=
    NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intro U V f; ext m; rfl)) (by intro M N f; ext U m; rfl)
  exact Functor.isoWhiskerRight (constantBridgeIso A X) H ≪≫
    Functor.isoWhiskerLeft (constantInternalPresheaves A X)
      (ConstantInternalModuleSheafEncoding.encSheafifyIso J B (internalToModule B) rfl) ≪≫
    Functor.isoWhiskerRight i (presheafToSheaf J (ModuleCat.{u + 1} B))

private def ordinaryModelIso (e : Encoding A X) :
    FiniteConstantModel.modelFunctor A X ⋙ e.ordinary.functor ⋙ e.fixed.functor ≅
      ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  Functor.isoWhiskerLeft _ (normalizedInternalIso A X e) ≪≫
    Functor.isoWhiskerRight (modelConstantInternalIso A X)
      (constantBridge A X ⋙ ConstantInternalModuleSheafEncoding.sheafEncoding
        (Scheme.ProEt.topology X) (ULift.{u + 1} A)
        (internalToModule (ULift.{u + 1} A)) rfl) ≪≫
    Functor.isoWhiskerLeft (FiniteConstantModel.scalarModules A) (constantInternalFixedIso A X) ≪≫
    Functor.isoWhiskerRight (scalarModulesIso A)
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))

private def smallSiteConstantIso :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⋙
        (IntegralFiniteEncoding.smallSiteSheafEquivalence X (ULift.{u + 1} A)).functor ≅
      constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  letI : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) :=
    IntegralFiniteEncoding.smallProEtaleDownDense X
  exact (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).constantSheafSheafCongrIso
    (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (proEtIsTerminal (proEtTerminal X))

private def smallFixedConstantIso :
    constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⋙
        (IntegralFiniteEncoding.smallFixedScalarsEquivalence X (ULift.{u + 1} A)).inverse ≅
      commutativeSiteConstantModuleFunctor
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1} A) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let B := ULift.{u + 1} A
  let E := IntegralFiniteEncoding.smallFixedScalarsEquivalence X B
  let i : commutativeSiteConstantModuleFunctor J B ⋙ E.functor ≅
      constantSheaf J (ModuleCat.{u + 1} B) :=
    moduleRestrictionConstantIso J B (SheafOfModules.constantCoefficientRing J B)
      (SheafOfModules.constantCoefficientUnit J B)
  exact Functor.fullyFaithfulCancelRight E.functor
    (Functor.isoWhiskerLeft (constantSheaf J (ModuleCat.{u + 1} B)) E.counitIso ≪≫
      Functor.rightUnitor _ ≪≫ i.symm)

private def modelEncodingIso (e : Encoding A X) :
    FiniteConstantModel.modelFunctor A X ⋙ IntegralFiniteEncoding.finiteEncodingFunctor A X e ≅
      ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom ⋙
        commutativeSiteConstantModuleFunctor
          (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1} A) :=
  Functor.isoWhiskerRight (ordinaryModelIso A X e)
      ((IntegralFiniteEncoding.smallSiteSheafEquivalence X (ULift.{u + 1} A)).functor ⋙
        (IntegralFiniteEncoding.smallFixedScalarsEquivalence X (ULift.{u + 1} A)).inverse) ≪≫
    Functor.isoWhiskerLeft
      (ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom)
      (Functor.isoWhiskerRight (smallSiteConstantIso A X)
        (IntegralFiniteEncoding.smallFixedScalarsEquivalence X (ULift.{u + 1} A)).inverse ≪≫
        smallFixedConstantIso A X)

end Comparisons

/-- The normalized encoding of the given small scalar realization is constant.

Source: Stacks Tags 03CY and 093J; integral local structure, proof step 2
(blueprint: lem-pe-integral-finite-constant-encoding).

Proof: compare the ordinary exact functors first. The constant-to-continuous coefficient
map is an isomorphism at a positive finite quotient. Extend a scalar module along this
map and pull it to X. The monoidal constant-sheaf comparison identifies its underlying
abelian sheaf with the constant sheaf of the same module. Normalization of e identifies
the action of every constant scalar. Since the constant coefficient unit is locally
surjective, this identifies the entire sheaf-of-rings action. Apply the AsSmall sheaf
comparison and the inverse fixed-scalar equivalence. Their constant-sheaf comparison
identifies the result with commutativeSiteConstantModuleFunctor. All comparisons are
natural in the module; apply them termwise and localize. Exact-derived composition
isomorphisms give the displayed square. The small complex is specified on both sides;
no descent or smallness inference from a slice object occurs.
-/
theorem integralFinite_constant_encoding
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (X : Scheme.{u})
      (e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X),
      Nonempty
        (integralFiniteScalarRealization l E X n ⋙
            IntegralFiniteEncoding.finiteEncodingDerived
              (Padic.coefficientExtensionRing l E (n + 1)) X e ≅
          (ModuleCat.uliftFunctor.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
              Padic.coefficientExtensionRing l E (n + 1)).symm :
            ModuleCat.{u + 1}
                (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) ≌
              ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
          ).mapDerivedCategory.inverse ⋙
          commutativeSiteDerivedConstantModuleFunctor
            (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro n X e
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ULift.{u + 1} A
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
  let U := ModuleCat.uliftFunctor.{u + 1, u} A
  let V : ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} B := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom
  let R : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A)
  let : V.IsLeftAdjoint := ⟨R.inverse, ⟨R.toAdjunction⟩⟩
  let : V.IsRightAdjoint := ⟨R.inverse, ⟨R.symm.toAdjunction⟩⟩
  let G := commutativeSiteConstantModuleFunctor
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) B
  let H := IntegralFiniteEncoding.finiteEncodingFunctor A X e
  let i : integralFiniteScalarFunctor l E X n ⋙ H ≅ U ⋙ V ⋙ G :=
    Functor.isoWhiskerLeft U (modelEncodingIso A X e)
  exact ⟨(Functor.mapDerivedCategoryCompIso (integralFiniteScalarFunctor l E X n) H).symm ≪≫
    Functor.mapDerivedCategoryNatIso i ≪≫
    Functor.mapDerivedCategoryCompIso U (V ⋙ G) ≪≫
    Functor.isoWhiskerLeft U.mapDerivedCategory (Functor.mapDerivedCategoryCompIso V G)⟩

end AlgebraicGeometry.ProEtale
