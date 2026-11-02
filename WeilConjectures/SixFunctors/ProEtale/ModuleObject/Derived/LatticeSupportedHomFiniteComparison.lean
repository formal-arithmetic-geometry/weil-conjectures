/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Finite-coefficient comparison for Hom from an extended lattice

Source: latest blueprint, sec-six-functors-basics, uniform constructible Ext proof,
Lattices, Torsion targets and Integral targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

Scalar extension is along the continuous quotient coefficient morphism; the target
category retains the quotient action. All derived categories are ordinary unbounded ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open DerivedNakayama

private theorem lisse_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (M : FormalSupportModules Λ T) (hM : IsLisseCoefficientModule Λ M) :
    LocallyFree (condensedRingObj Λ T) M := by
  obtain ⟨C, hC⟩ := hM
  exact ⟨C, fun c ↦ (freeAt_iff_standard Λ (C.f c) M).mpr (hC c)⟩

private theorem locallyFree_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (M : FormalSupportModules Λ T) (hM : LocallyFree (condensedRingObj Λ T) M) :
    IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := hM
  exact ⟨C, fun c ↦ (freeAt_iff_standard Λ (C.f c) M).mp (hC c)⟩

private theorem lisse_dualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (M : FormalSupportModules Λ T) (hM : IsLisseCoefficientModule Λ M) :
    IsDualizable M := by
  apply coverRetract_dualizable Λ T M
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun c ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hC c
  let e' := ((normalizedPullbackIso Λ (C.f c)).app M).symm ≪≫ e
  exact ⟨r, ⟨⟨e'.hom, e'.inv, e'.hom_inv_id⟩⟩⟩

private theorem lisse_scalar
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {T : Scheme.{u}}
    (M : FormalSupportModules Λ T) (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ' ((Mod.extendScalars (coefficientMap a T)).obj M) := by
  apply locallyFree_lisse
  exact WeilConjectures.SixFunctors.integralModel_locallyFree_scalar a T M
    (lisse_locallyFree Λ M hM)

private theorem dual_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (M : FormalSupportModules Λ T) (hM : IsDualizable M) :
    ObjectProperty.flat ((ihom M).obj (𝟙_ (FormalSupportModules Λ T))) := by
  obtain ⟨hd⟩ := hM
  let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
  have hflat : ObjectProperty.flat Mᘁ := by
    let : HasRightDual Mᘁ := ⟨M⟩
    exact (isDualizable_of_hasRightDual Mᘁ).flat
  exact ObjectProperty.prop_of_iso ObjectProperty.flat
    (MonoidalClosed.ihomObjUnitIso Mᘁ M).symm hflat

private noncomputable def scalarDualIso
    {T : Scheme.{u}} {R A : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
    (φ : R ⟶ A) [IsMonHom φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)
    (hM : IsDualizable M) :
    (Mod.extendScalars φ).obj ((ihom M).obj (𝟙_ _)) ≅
      (ihom ((Mod.extendScalars φ).obj M)).obj (𝟙_ _) := by
  let F := Mod.extendScalars φ
  let := Mod.extendScalarsMonoidal φ
  let hd := Classical.choice hM
  let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom Mᘁ M M
  let D := (ihom M).obj (𝟙_ _)
  let : ExactPairing D M := MonoidalClosed.exactPairingOfIsIso M
  let : ExactPairing (F.obj D) (F.obj M) := ExactPairing.map F D M
  exact asIso (MonoidalClosed.curry (ε_ (F.obj D) (F.obj M)))

private theorem scalarDualIso_evaluation
    {T : Scheme.{u}} {R A : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
    (φ : R ⟶ A) [IsMonHom φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)
    (hM : IsDualizable M) :
    (((Mod.extendRestrictAdjunction φ).unit.app M).hom ⊗ₘ
        (((Mod.extendRestrictAdjunction φ).unit.app ((ihom M).obj (𝟙_ _))).hom ≫
          (scalarDualIso φ M hM).hom.hom)) ≫
      Mod.tensorObjπ ((Mod.extendScalars φ).obj M)
        ((ihom ((Mod.extendScalars φ).obj M)).obj (𝟙_ _)) ≫
      ((ihom.ev ((Mod.extendScalars φ).obj M)).app (𝟙_ _)).hom =
    Mod.tensorObjπ M ((ihom M).obj (𝟙_ _)) ≫
      ((ihom.ev M).app (𝟙_ _)).hom ≫ φ := by
  let F := Mod.extendScalars φ
  let := Mod.extendScalarsMonoidal φ
  let D := (ihom M).obj (𝟙_ _)
  let e := scalarDualIso φ M hM
  have he : (F.obj M ◁ e.hom) ≫ (ihom.ev (F.obj M)).app (𝟙_ _) =
      Functor.LaxMonoidal.μ F M D ≫ F.map ((ihom.ev M).app (𝟙_ _)) ≫
        Functor.OplaxMonoidal.η F := by
    let hd := Classical.choice hM
    let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) :=
      MonoidalClosed.isIso_ihomUnitTensorToIhom Mᘁ M M
    let : ExactPairing D M := MonoidalClosed.exactPairingOfIsIso M
    let : ExactPairing (F.obj D) (F.obj M) := ExactPairing.map F D M
    exact MonoidalClosed.uncurry_curry (ε_ (F.obj D) (F.obj M))
  have hδ : Mod.tensorObjπ M D ≫ Mod.extendUnitHom φ (M ⊗ D) ≫
      (Functor.OplaxMonoidal.δ F M D).hom =
      (Mod.extendUnitHom φ M ⊗ₘ Mod.extendUnitHom φ D) ≫
        Mod.tensorObjπ (F.obj M) (F.obj D) := by
    dsimp only [F]
    rw [Mod.extendScalarsOplaxMonoidal_δ]
    rw [Mod.extendUnitHom_extendHom, Mod.comp_hom',
      Mod.tensorObjπ_tensorHom_hom_whisker_assoc, Mod.tensorObjπ_comapTensorHom_hom]
    rfl
  have hη : Mod.extendUnitHom φ (𝟙_ _) ≫ (Functor.OplaxMonoidal.η F).hom = φ := by
    dsimp only [F]
    rw [Mod.extendScalarsOplaxMonoidal_η]
    rw [Mod.extendUnitHom_extendHom, Mod.comapUnitHom_hom]
  rw [Mod.extendRestrictAdjunction_unit_app_hom,
    Mod.extendRestrictAdjunction_unit_app_hom]
  change (Mod.extendUnitHom φ M ⊗ₘ (Mod.extendUnitHom φ D ≫ e.hom.hom)) ≫ _ ≫ _ = _
  have ht := tensorHom_comp_tensorHom (Mod.extendUnitHom φ M)
    (Mod.extendUnitHom φ D) (𝟙 _) e.hom.hom
  simp only [Category.comp_id] at ht
  erw [← ht, Category.assoc]
  rw [id_tensorHom]
  erw [← Mod.tensorObjπ_whiskerLeft_assoc, ← Mod.comp_hom', he]
  simp only [Mod.comp_hom']
  erw [← reassoc_of% hδ]
  have hδμ := congrArg Mod.Hom.hom (Functor.Monoidal.δ_μ F M D)
  simp only [Mod.comp_hom', Mod.id_hom'] at hδμ
  erw [reassoc_of% hδμ]
  change Mod.tensorObjπ M D ≫ Mod.extendUnitHom φ (M ⊗ D) ≫
    (Mod.extendScalarsMap φ ((ihom.ev M).app (𝟙_ _))).hom ≫ _ = _
  erw [Mod.extendUnitHom_extendScalarsMap_assoc, hη]


set_option maxHeartbeats 3000000 in
-- Reconstruct section-module equivalences and compare their complex-valued functors.
private theorem restriction_sections_quasiIso
    {T : Scheme.{u}} {R A : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
    (φ : R ⟶ A) [IsMonHom φ]
    (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A) ℤ)
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) ℤ)
    (f : ((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso f] :
    QuasiIso (((Mod.forget R ⋙
      Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).mapHomologicalComplex (.up ℤ)).map f) := by
  let J := Scheme.ProEt.topology T
  let ER := (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor
  let EA := (InternalAbelianSheafModule.sectionModuleEquivalence J A).functor
  have : ER.IsEquivalence := Equivalence.isEquivalence_functor
    (InternalAbelianSheafModule.sectionModuleEquivalence J R)
  have : EA.IsEquivalence := Equivalence.isEquivalence_functor
    (InternalAbelianSheafModule.sectionModuleEquivalence J A)
  have : ER.Additive := Functor.additive_of_preserves_binary_products ER
  have : EA.Additive := Functor.additive_of_preserves_binary_products EA
  let e := InternalAbelianSheafModule.scalarRestrictionIso J φ
  let I' := (EA.mapHomologicalComplex (.up ℤ)).obj I
  let K' := (ER.mapHomologicalComplex (.up ℤ)).obj K
  let f' := (NatIso.mapHomologicalComplex e (.up ℤ)).inv.app I ≫
    (ER.mapHomologicalComplex (.up ℤ)).map f
  have : CochainComplex.IsKInjective I' := inferInstance
  have : CochainComplex.IsKInjective K' := inferInstance
  have : QuasiIso f' := by
    dsimp only [f']
    infer_instance
  have hf := SheafOfModules.coefficientRestrictionSections_quasiIso.{u + 1, u, u + 1}
    (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J φ) I' K' f'
  let G := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)) ⋙
    sheafToPresheaf J Ab.{u + 1} ⋙ lim
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have hf' : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
      ((ER.mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [show (G.mapHomologicalComplex (.up ℤ)).map f' =
      (G.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex e (.up ℤ)).inv.app I) ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        ((ER.mapHomologicalComplex (.up ℤ)).map f) from Functor.map_comp _ _ _] at hf
    exact (quasiIso_iff_comp_left _ _).mp hf
  let H := Mod.forget R ⋙ Sheaf.Γ J Ab.{u + 1}
  let eΓ : ER ⋙ G ≅ H := Functor.isoWhiskerLeft (Mod.forget R)
    (Sheaf.ΓNatIsoLim J Ab.{u + 1}).symm
  have : QuasiIso (((ER ⋙ G).mapHomologicalComplex (.up ℤ)).map f) := hf'
  exact SheafOfModules.quasiIso_map_iso (ER ⋙ G) H eΓ f

private noncomputable def restrictionDerivedSectionsIso
    [HasDerivedCategory.{u + 1} Ab.{u + 1}]
    {T : Scheme.{u}} {R A : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
    (φ : R ⟶ A) [IsMonHom φ] :
    (Mod.comap φ).mapDerivedCategory ⋙
        (Mod.forget R ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerivedFunctor ≅
      (Mod.forget A ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerivedFunctor := by
  let ΓR := Mod.forget R ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}
  let ΓA := Mod.forget A ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}
  let α : ΓA ≅ Mod.comap φ ⋙ ΓR :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let σ := Functor.rightDerivedPullback (Mod.comap φ) α.hom
  have hσI (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A) ℤ)
      [I.IsKInjective] : IsIso (σ.app (DerivedCategory.Q.obj I)) := by
    obtain ⟨K, hK, f, _, hf⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective
        (((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj I)
    have : K.IsKInjective := hK
    have : QuasiIso f := hf
    have : QuasiIso ((ΓR.mapHomologicalComplex (.up ℤ)).map f) :=
      restriction_sections_quasiIso φ I K f
    have h := Functor.rightDerivedPullback_app_Q_obj (Mod.comap φ) α.hom I K f
    have : IsIso (σ.app (DerivedCategory.Q.obj I) ≫ ΓR.rightDerivedFunctor.map
        ((Mod.comap φ).mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map f)) := by
      have : IsIso ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) :=
        inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex α (.up ℤ)).app I).hom)
      have : QuasiIso ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I ≫
          (ΓR.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
      rw [h]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp this
  have (Y : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A)) :
      IsIso (σ.app Y) := by
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Y
    have : I.IsKInjective := hI
    have := hσI I
    have : IsIso (σ.app Y ≫
        ((Mod.comap φ).mapDerivedCategory ⋙ ΓR.rightDerivedFunctor).map e.hom) := by
      rw [← σ.naturality]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp this
  have : IsIso σ := NatIso.isIso_of_isIso_app _
  exact (asIso σ).symm

private noncomputable def scalarDerivedHomIso
    {T : Scheme.{u}} {R A : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
    (φ : R ⟶ A) [IsMonHom φ]
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    (Mod.comap φ).mapDerivedCategory ⋙ ihom Q ≅
      ihom ((Mod.extendScalars φ).leftDerivedFunctor.obj Q) ⋙
        (Mod.comap φ).mapDerivedCategory := by
  let F := Mod.extendScalars φ
  let := Mod.extendScalarsMonoidal φ
  let LF := F.leftDerivedFunctor
  let μ := Functor.normalizedTensorIso F LF (Iso.refl _)
  let e : LF ⋙ tensorLeft (LF.obj Q) ≅ tensorLeft Q ⋙ LF :=
    NatIso.ofComponents (fun N ↦ μ Q N) (by
      intro N N' f
      exact Functor.normalizedTensorIso_natural₂ F LF (Iso.refl _) Q f)
  let a := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  exact (((ihom.adjunction Q).comp a).ofNatIsoLeft e.symm).rightAdjointUniq
    (a.comp (ihom.adjunction (LF.obj Q)))

private noncomputable def sectionsCoyonedaIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    formalClosedSupportSections Λ T ≅
      preadditiveCoyoneda.obj (op (𝟙_ (FormalSupportModules Λ T))) := by
  let P := Scheme.ProEt.mk (𝟙 T)
  have hP : IsTerminal P :=
    IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom) fun V f ↦
      MorphismProperty.Over.Hom.ext <| by
        change f.left = V.hom
        rw [← MorphismProperty.Over.w f]
        exact (Category.comp_id _).symm
  exact Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ T))
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) Ab.{u + 1} hP) ≪≫
      (regularSectionsIso T Λ).symm

private noncomputable def flatGlobalHomIso
    [HasDerivedCategory.{u + 1} Ab.{u + 1}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (M : FormalSupportModules Λ T) (hM : ObjectProperty.flat M) :
    (derivedHom Λ T).obj
        (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ T) 0).obj M)) ⋙
        (formalClosedSupportSections Λ T).rightDerivedFunctor ≅
      (preadditiveCoyoneda.obj (op M)).rightDerivedFunctor := by
  have : PreservesFiniteLimits (tensorLeft M) := hM.1.1
  have : (ihom M).PreservesKInjectiveComplexes :=
    (ihom.adjunction M).preservesKInjectiveComplexes
  let a := (ihom.adjunction M).derivedAdjunction.ofNatIsoLeft (derivedTensorSingleIso M)
  let e : (derivedHom Λ T).obj
      (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ T) 0).obj M)) ≅
      (ihom M).rightDerivedFunctor :=
    (derivedTensorHomAdjunction Λ
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ T) 0).obj M)).rightAdjointUniq a
  let eΓ : ihom M ⋙ formalClosedSupportSections Λ T ≅
      preadditiveCoyoneda.obj (op M) :=
    Functor.isoWhiskerLeft (ihom M) (sectionsCoyonedaIso Λ T) ≪≫
      ((ihom.adjunction M).preadditiveCoyonedaObjIso (𝟙_ _)).symm ≪≫
      preadditiveCoyoneda.mapIso (ρ_ M).op.symm
  exact Functor.isoWhiskerRight e (formalClosedSupportSections Λ T).rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' _ _ eΓ

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
  {S Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (v : S ⟶ Z)
  [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion v]
  (L : FormalSupportModules (integerRing l E) S)

set_option maxHeartbeats 600000 in
-- Elaborate the full natural-isomorphism package without unfolding closed derived structures.
/-- The full comparison package, including evaluation normalization of the reduced dual,
source reduction in D(A_n), derived global Hom, and all three natural abelian-group maps.
Source: latest blueprint uniform constructible Ext proof, Lattices/Torsion/Integral targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

The evaluation equation is an equation of underlying abelian-sheaf morphisms. The two
adjunction units send x and a functional to their reductions; after the displayed dual
isomorphism, evaluating them is exactly evaluation over R followed by R → A. Thus the
isomorphism cannot be an arbitrary rescaling. The ordinary quotient module is scalar
extension along the quotient, so Ln and Dn mean L/pi^n and its reduced integral dual.
The natural transformations in `groups` have abelian-group morphism components. -/
structure LatticeSupportedHomFiniteComparison where
  finite : Finite (Padic.coefficientExtensionRing l E n)
  torsion : ∃ m : ℕ, ∀ x : Padic.coefficientExtensionRing l E n, (l ^ m) • x = 0
  reduced_lisse : IsLisseCoefficientModule (quotientRing l E n) ((Mod.extendScalars
      (coefficientMap (reductionRing l E n) S)).obj L)
  dualReduction : ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj ((ihom L).obj
      (𝟙_ (FormalSupportModules (integerRing l E) S)))) ≅ (ihom ((Mod.extendScalars
      (coefficientMap (reductionRing l E n) S)).obj L)).obj (𝟙_ (FormalSupportModules
      (quotientRing l E n) S))
  evaluation :
    (((Mod.extendRestrictAdjunction (coefficientMap (reductionRing l E n) S)).unit.app L).hom ⊗ₘ
        (((Mod.extendRestrictAdjunction (coefficientMap (reductionRing l E n) S)).unit.app ((ihom
            L).obj (𝟙_ (FormalSupportModules (integerRing l E) S)))).hom ≫ dualReduction.hom.hom))
            ≫
      Mod.tensorObjπ ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj L) ((ihom
          ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj L)).obj (𝟙_
          (FormalSupportModules (quotientRing l E n) S))) ≫
        ((ihom.ev ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj L)).app (𝟙_
            (FormalSupportModules (quotientRing l E n) S))).hom =
      Mod.tensorObjπ L ((ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E) S))) ≫ ((ihom.ev
          L).app (𝟙_ (FormalSupportModules (integerRing l E) S))).hom ≫ (coefficientMap
          (reductionRing l E n) S)
  sourceReduction : ((Mod.extendScalars (coefficientMap (reductionRing l E n)
      X)).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor (FormalSupportModules
      (integerRing l E) X) 0).obj ((lowerStar (integerRing l E) i).obj ((openImmersionLowerShriek
      (integerRing l E) v).obj L)))) ≅ (DerivedCategory.singleFunctor (FormalSupportModules
      (quotientRing l E n) X) 0).obj ((lowerStar (quotientRing l E n) i).obj
      ((openImmersionLowerShriek (quotientRing l E n) v).obj ((Mod.extendScalars (coefficientMap
      (reductionRing l E n) S)).obj L)))
  derivedComparison : Nonempty
    ((Mod.comap (coefficientMap (reductionRing l E n) X)).mapDerivedCategory ⋙ (derivedHom
        (integerRing l E) X).obj (op ((DerivedCategory.singleFunctor (FormalSupportModules
        (integerRing l E) X) 0).obj ((lowerStar (integerRing l E) i).obj
        ((openImmersionLowerShriek (integerRing l E) v).obj L)))) ⋙
        (formalClosedSupportSections (integerRing l E) X).rightDerivedFunctor ≅
            ((formalClosedSupport (quotientRing l E n) i j).rightDerivedFunctor ⋙
            (formalSupportPullback (quotientRing l E n) v).mapDerivedCategory ⋙ (derivedTensor
            (quotientRing l E n) S).obj ((DerivedCategory.singleFunctor (FormalSupportModules
            (quotientRing l E n) S) 0).obj ((Mod.extendScalars (coefficientMap (reductionRing l E
            n) S)).obj ((ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E) S))))) ⋙
            (formalClosedSupportSections (quotientRing l E n) S).rightDerivedFunctor))
  groups : ∀ q : ℤ,
    ∃ e₁ : shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q ⋙
        (Mod.comap (coefficientMap (reductionRing l E n) X)).mapDerivedCategory ⋙
            preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor (FormalSupportModules
            (integerRing l E) X) 0).obj ((lowerStar (integerRing l E) i).obj
            ((openImmersionLowerShriek (integerRing l E) v).obj L)))) ≅
      shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q ⋙
        preadditiveCoyoneda.obj (op ((Mod.extendScalars (coefficientMap (reductionRing l E n)
            X)).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor (FormalSupportModules
            (integerRing l E) X) 0).obj ((lowerStar (integerRing l E) i).obj
            ((openImmersionLowerShriek (integerRing l E) v).obj L))))),
      (∀ (K : DerivedCategory (FormalSupportModules (quotientRing l E n) X))
        (f : (DerivedCategory.singleFunctor (FormalSupportModules (integerRing l E) X) 0).obj
            ((lowerStar (integerRing l E) i).obj ((openImmersionLowerShriek (integerRing l E)
            v).obj L)) ⟶ (Mod.comap (coefficientMap (reductionRing l E n)
            X)).mapDerivedCategory.obj (K⟦q⟧)),
        (e₁.hom.app K) f =
          ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (reductionRing l E n)
              X)).homEquiv _ _).symm f) ∧
      ∃ e₂ : shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q ⋙
          preadditiveCoyoneda.obj (op ((Mod.extendScalars (coefficientMap (reductionRing l E n)
              X)).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor (FormalSupportModules
              (integerRing l E) X) 0).obj ((lowerStar (integerRing l E) i).obj
              ((openImmersionLowerShriek (integerRing l E) v).obj L))))) ≅
        shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor (FormalSupportModules
              (quotientRing l E n) X) 0).obj ((lowerStar (quotientRing l E n) i).obj
              ((openImmersionLowerShriek (quotientRing l E n) v).obj ((Mod.extendScalars
              (coefficientMap (reductionRing l E n) S)).obj L))))),
        (∀ (K : DerivedCategory (FormalSupportModules (quotientRing l E n) X)) (f :
            ((Mod.extendScalars (coefficientMap (reductionRing l E n) X)).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor (FormalSupportModules (integerRing l E) X) 0).obj
            ((lowerStar (integerRing l E) i).obj ((openImmersionLowerShriek (integerRing l E)
            v).obj L)))) ⟶ K⟦q⟧),
          (e₂.hom.app K) f = sourceReduction.inv ≫ f) ∧
        Nonempty (shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q ⋙
            preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor (FormalSupportModules
                (quotientRing l E n) X) 0).obj ((lowerStar (quotientRing l E n) i).obj
                ((openImmersionLowerShriek (quotientRing l E n) v).obj ((Mod.extendScalars
                (coefficientMap (reductionRing l E n) S)).obj L))))) ≅
          ((formalClosedSupport (quotientRing l E n) i j).rightDerivedFunctor ⋙
              (formalSupportPullback (quotientRing l E n) v).mapDerivedCategory ⋙ (derivedTensor
              (quotientRing l E n) S).obj ((DerivedCategory.singleFunctor (FormalSupportModules
              (quotientRing l E n) S) 0).obj ((Mod.extendScalars (coefficientMap (reductionRing l
              E n) S)).obj ((ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E) S))))) ⋙
              (formalClosedSupportSections (quotientRing l E n) S).rightDerivedFunctor) ⋙
              DerivedCategory.homologyFunctor Ab.{u + 1} q)
  termwise : ∃ h : PreservesFiniteLimits (tensorLeft ((Mod.extendScalars (coefficientMap
      (reductionRing l E n) S)).obj ((ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E)
      S))))),
    letI := h
    Nonempty ((tensorLeft ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj ((ihom
        L).obj (𝟙_ (FormalSupportModules (integerRing l E) S))))).mapDerivedCategory ≅
        (derivedTensor (quotientRing l E n) S).obj ((DerivedCategory.singleFunctor
        (FormalSupportModules (quotientRing l E n) S) 0).obj ((Mod.extendScalars (coefficientMap
        (reductionRing l E n) S)).obj ((ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E)
        S))))))

set_option maxHeartbeats 1000000 in
-- Assemble the natural isomorphisms without unfolding the derived closed structures.
/-- Hom out of an integral lattice extended by zero is computed with finite coefficients
and the reduced-dual supported complex, naturally in every unbounded target.
Source: latest blueprint uniform constructible Ext proof, Integral targets and Torsion targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

Proof:
1. The coefficient-extension DVR has finite quotients. The extended l-adic norm puts l
in the uniformizer ideal, so l^n annihilates the nth quotient.
2. Identify lisse modules with the existing locally finite free models. Scalar extension
preserves these models. The integral-model flatness and scalar comparison identify the
left-derived reduction of i_*v_!L with the single complex of i_*v_! of its reduction.
3. A lisse module is dualizable. Transport its canonical internal dual pairing through
the strong monoidal scalar functor and curry its evaluation. The scalar units, oplax
structure and triangle identities give exactly the displayed evaluation normalization.
4. The derived tensor comparison for a right exact scalar functor, together with derived
extension/restriction adjunction, identifies scalar restriction of internal Hom with Hom
out of the derived scalar extension. Restriction commutes with derived global sections:
transfer to sectionwise modules and apply coefficient-restriction sections acyclicity to
K-injective resolutions. This does not assert that restriction preserves K-injectivity.
5. Apply the formal closed-support stratum formula to the reduced lattice, substituting
the dual comparison. The derived scalar adjunction gives the first group isomorphism;
precomposition with sourceReduction.inv gives the second, with the required formulas.
Derived additive coyoneda evaluation and the stratum formula give the third, naturally
in every unbounded complex and every shift. The dual is flat by dualizability and remains
flat under scalar extension, so its ordinary termwise tensor computes derived tensor. -/
theorem latticeSupportedHomFiniteComparison
    (hn : 1 ≤ n) (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hpl : p ≠ l)
    [S.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [V.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [v.IsOver (Spec (.of k))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hL : IsLisseCoefficientModule (integerRing l E) L) :
    Nonempty (LatticeSupportedHomFiniteComparison l E n i j v L) := by
  classical
  have : IsGrothendieckAbelian.{u + 1} Ab.{u + 1} := inferInstance
  let : HasDerivedCategory.{u + 1} Ab.{u + 1} :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hred := lisse_scalar (reductionRing l E n) L hL
  have hflat := WeilConjectures.SixFunctors.integralModel_extension_flat
    (integerRing l E) v i L (lisse_locallyFree _ L hL)
  obtain ⟨es⟩ := WeilConjectures.SixFunctors.integralModel_flat_derived_single
    (coefficientMap (reductionRing l E n) X) _ hflat
  let esource := es ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    (WeilConjectures.SixFunctors.integralModel_extension_scalar (reductionRing l E n) v i L)
  have : TopologicalSpace.NoetherianSpace V :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  let Ln := (Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj L
  let Qn := (lowerStar (quotientRing l E n) i).obj
    ((openImmersionLowerShriek (quotientRing l E n) v).obj Ln)
  have hflatn : ObjectProperty.flat Qn :=
    WeilConjectures.SixFunctors.integralModel_extension_flat
      (quotientRing l E n) v i Ln (lisse_locallyFree _ Ln hred)
  let edual := scalarDualIso (coefficientMap (reductionRing l E n) S) L
    (lisse_dualizable _ L hL)
  obtain ⟨fs⟩ := formalClosedSupportAssertions (quotientRing l E n) l k p hpl i j hij
  obtain ⟨ef⟩ := fs.stratum v Ln (by
    obtain ⟨C, hC⟩ := hred
    refine ⟨C, fun c ↦ ?_⟩
    obtain ⟨r, ⟨e⟩⟩ := hC c
    let e' := ((normalizedPullbackIso (quotientRing l E n) (C.f c)).app Ln).symm ≪≫ e
    exact ⟨r, ⟨⟨e'.hom, e'.inv, e'.hom_inv_id⟩⟩⟩)
  let et := (derivedTensor (quotientRing l E n) S).mapIso
    ((DerivedCategory.singleFunctor (FormalSupportModules (quotientRing l E n) S) 0).mapIso
      edual.symm)
  let ΓS : DerivedCategory (FormalSupportModules (quotientRing l E n) S) ⥤
      DerivedCategory.{u + 1} Ab.{u + 1} :=
    (formalClosedSupportSections (quotientRing l E n) S).rightDerivedFunctor
  let efinal := ef ≪≫ Functor.isoWhiskerLeft
    (formalClosedSupport (quotientRing l E n) i j).rightDerivedFunctor
    (Functor.isoWhiskerLeft (formalSupportPullback (quotientRing l E n) v).mapDerivedCategory
      (Functor.isoWhiskerRight et ΓS))
  let eglobal := (flatGlobalHomIso (quotientRing l E n) X Qn hflatn).symm ≪≫ efinal
  refine ⟨{
    finite := Padic.finite_coefficientExtensionRing l E n hn
    torsion := ?_
    reduced_lisse := hred
    dualReduction := edual
    evaluation := ?_
    sourceReduction := esource
    derivedComparison := ?_
    groups := ?_
    termwise := ?_ }⟩
  · have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
    have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hl : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      rw [← map_natCast (algebraMap (Padic l) E) l]
      change spectralNorm (Padic l) E ((algebraMap (Padic l) E) (l : Padic l)) < 1
      rw [spectralNorm_extends]
      exact Padic.norm_p_lt_one
    have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
        Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
      rw [hgen]
      exact (h.2.1 _).mpr hl
    have hz : (l : Padic.coefficientExtensionRing l E n) ^ n = 0 := by
      change (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (l : Padic.coefficientExtensionIntegers l E)) ^ n = 0
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hm n)
    refine ⟨n, fun x ↦ ?_⟩
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  · exact scalarDualIso_evaluation _ L (lisse_dualizable _ L hL)
  · let Q := (DerivedCategory.singleFunctor (FormalSupportModules (integerRing l E) X) 0).obj
      ((lowerStar (integerRing l E) i).obj
        ((openImmersionLowerShriek (integerRing l E) v).obj L))
    let eh := scalarDerivedHomIso (coefficientMap (reductionRing l E n) X) Q
    let eh' := (derivedHom (quotientRing l E n) X).mapIso esource.symm.op
    exact ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eh ≪≫
        Functor.isoWhiskerRight eh' (Mod.comap (coefficientMap
          (reductionRing l E n) X)).mapDerivedCategory)
        (formalClosedSupportSections (integerRing l E) X).rightDerivedFunctor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (restrictionDerivedSectionsIso (coefficientMap (reductionRing l E n) X)) ≪≫ efinal⟩
  · intro q
    let a := Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (reductionRing l E n) X)
    have : Functor.IsLeftAdjoint
        (Mod.extendScalars (coefficientMap (reductionRing l E n) X)).leftDerivedFunctor :=
      a.isLeftAdjoint
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (Mod.extendScalars (coefficientMap (reductionRing l E n) X)).leftDerivedFunctor
    have : Functor.Additive
        (Mod.extendScalars (coefficientMap (reductionRing l E n) X)).leftDerivedFunctor :=
      Functor.additive_of_preservesBinaryBiproducts _
    let Q := (DerivedCategory.singleFunctor (FormalSupportModules (integerRing l E) X) 0).obj
      ((lowerStar (integerRing l E) i).obj ((openImmersionLowerShriek
        (integerRing l E) v).obj L))
    let e₁ := Functor.isoWhiskerLeft
      (shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q)
      (a.preadditiveCoyonedaObjIso Q).symm
    let e₂ := Functor.isoWhiskerLeft
      (shiftFunctor (DerivedCategory (FormalSupportModules (quotientRing l E n) X)) q)
      (preadditiveCoyoneda.mapIso esource.symm.op)
    refine ⟨e₁, ?_, e₂, ?_, ?_⟩
    · intro K f
      rfl
    · intro K f
      rfl
    · obtain ⟨e⟩ := CategoryTheory.derived_coyoneda_evaluation Qn q
      exact ⟨e ≪≫ Functor.isoWhiskerRight eglobal (DerivedCategory.homologyFunctor Ab.{u + 1} q)⟩
  · let D := (ihom L).obj (𝟙_ (FormalSupportModules (integerRing l E) S))
    have hD : ObjectProperty.flat D := dual_flat _ L (lisse_dualizable _ L hL)
    have hE : ObjectProperty.flat
        ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj D) :=
      Functor.PreservesFlat.flat_obj hD
    have ht : PreservesFiniteLimits (tensorLeft
        ((Mod.extendScalars (coefficientMap (reductionRing l E n) S)).obj D)) := hE.1.1
    exact ⟨ht, ⟨(tensorLeft _).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      derivedTensorSingleIso _⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
