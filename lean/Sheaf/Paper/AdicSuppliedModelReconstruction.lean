/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.LevelwiseAdicTruncations
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import all WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import all Sheaf.Paper.CompletedKoszulConstantTransport
import Sheaf.Paper.WeilCompletedKoszulLimitComparison
import all Sheaf.Paper.CompletedConstantCoefficientEquivalence
import all Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedRlimFunctor
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.CompletedKoszulQuotientComparison
import Sheaf.Paper.IntrinsicCompletion
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.Paper.ConstructibleCoefficientSerre
import all Sheaf.Paper.TorsionLimitSheafCompleteness
import all Sheaf.Paper.ConstantScalarDirectImageCompleteness
import Sheaf.Paper.LocalCompletenessModels
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal


/-! # Reconstruction of one supplied bounded adic model

Source: integral truncations, supplied-model comparison, steps 9--10.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

private noncomputable def restrictedAbelianInverseImageIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] :
    proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ≅
      (MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
        (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (ProEt.topology Y) (ProEt.topology X) := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) _root_.trivial).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (ProEt.topology Y) (ProEt.topology X)
  exact (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).leftAdjointUniq a

private noncomputable def compositeAbelianInverseImageIso
    {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    proEtaleSheafInverseImage (f ≫ g) AddCommGrpCat.{u + 1} ≅
      proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).comp
    (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1})
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    AddCommGrpCat.{u + 1} (ProEt.topology X) (ProEt.topology Y) (ProEt.topology Z)
  exact (proEtaleSheafAdjunction (f ≫ g) AddCommGrpCat.{u + 1}).leftAdjointUniq
    (a.ofNatIsoRight e)

private theorem restrictedAbelianInverseImageLimits
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i] (U : Y.ProEt) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage (U.hom ≫ i) AddCommGrpCat.{u + 1}) := by
  let hImm : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}) := immersion_abelianLimits i
  let hEt : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}) :=
    preservesLimits_of_natIso (restrictedAbelianInverseImageIso U.hom).symm
  let hc : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage i AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.comp_preservesLimits _ _
  exact (preservesLimitsOfSize_iff_of_natIso
    (compositeAbelianInverseImageIso U.hom i).symm).mp hc

private theorem restrictedModuleInverseImageLimits
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i] (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleModuleInverseImage (U.hom ≫ i) R) := by
  let := restrictedAbelianInverseImageLimits i U
  let R' := (adicLisseForget U.left).obj
    ((proEtaleSheafInverseImage (U.hom ≫ i) CommRingCat.{u + 1}).obj R)
  let := forgetModule_preservesLimits ((adicLisseForget X).obj R)
  let := forgetModule_preservesLimits R'
  let V := SheafOfModules.toSheaf R'
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  obtain ⟨⟨e⟩, _⟩ := proEtale_moduleInverseImage_comparison (U.hom ≫ i) R
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleModuleInverseImage (U.hom ≫ i) R ⋙ V) :=
    preservesLimits_of_natIso e.symm
  exact preservesLimits_of_reflects_of_preserves _ V

private theorem restrictedRingModulePullbackLimits
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i] (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleRingModulePullback (U.hom ≫ i) R
        ((adicTowerInverseImage (U.hom ≫ i)).obj R) (Iso.refl _)) := by
  let := restrictedModuleInverseImageLimits i U R
  let := proEtaleRingExtension_preservesLimits (U.hom ≫ i) R
    ((adicTowerInverseImage (U.hom ≫ i)).obj R) (Iso.refl _)
  exact @comp_preservesLimits _ _ _ _ _ _
    (proEtaleModuleInverseImage (U.hom ≫ i) R) _
    (restrictedModuleInverseImageLimits i U R)
    (proEtaleRingExtension_preservesLimits (U.hom ≫ i) R
      ((adicTowerInverseImage (U.hom ≫ i)).obj R) (Iso.refl _))

private theorem moduleCountableAB4Star (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CountableAB4Star (pbcModules X R) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  have : (lim (J := Discrete ℕ) (C := pbcModules X R)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} X R).2.2 ℕ (fun n ↦ F.obj ⟨n⟩)
            (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  let : HasFiniteBiproducts (pbcModules X R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have := hasExactLimitsOfShape_of_preservesEpi (pbcModules X R) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

private theorem exactFunctor_derived_products
    {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasCountableProducts B] [HasCountableProducts C]
    [CountableAB4Star B] [CountableAB4Star C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  have hQ (E : ℕ → CochainComplex C ℤ) :
      PreservesLimit (Discrete.functor E) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      (derivedCategory_termwiseProduct_isLimit C ℕ E).some
  let : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := C)) :=
    preservesLimitsOfShape_of_discrete _
  let : PreservesLimitsOfShape (Discrete ℕ) (F.mapHomologicalComplex (.up ℤ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i ↦
      preservesLimitsOfShape_of_natIso
        (show HomologicalComplex.eval B (.up ℤ) i ⋙ F ≅
            F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.eval C (.up ℤ) i from
          NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp))
  let : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact preservesProductsOfEssSurj ℕ DerivedCategory.Q F.mapDerivedCategory
    (derivedCategory_termwiseProduct_isLimit B ℕ)

private theorem restrictedDerivedInverseImageProducts
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i] (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesLimitsOfShape (Discrete ℕ) (adicTowerPullback (U.hom ≫ i) R) := by
  let R' := (adicTowerInverseImage (U.hom ≫ i)).obj R
  let : CountableAB4Star (pbcModules X R) := moduleCountableAB4Star X R
  let : CountableAB4Star (pbcModules U.left R') := moduleCountableAB4Star U.left R'
  let := restrictedRingModulePullbackLimits i U R
  let : PreservesLimitsOfSize.{0, 0}
      (proEtaleRingModulePullback (U.hom ≫ i) R R' (Iso.refl _)) :=
    preservesLimitsOfSize_shrink _
  exact exactFunctor_derived_products
    (B := pbcModules X R) (C := pbcModules U.left R')
    (proEtaleRingModulePullback (U.hom ≫ i) R R' (Iso.refl _))

private theorem roos_change_vertex
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {M : ℕ → C} [HasProduct M] (f : ∀ n, M (n + 1) ⟶ M n)
    {K P : C} (e : K ≅ P) (p : P ⟶ ∏ᶜ M) (δ : ∏ᶜ M ⟶ P⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f P p δ) : IsDerivedLimit f K := by
  refine ⟨e.hom ≫ p, δ ≫ e.inv⟦(1 : ℤ)⟧', ?_⟩
  exact Pretriangulated.isomorphic_distinguished _ h _
    (Pretriangulated.Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))

private theorem roos_congr
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasProductsOfShape ℕ D] {M N : ℕ → D}
    (v : ∀ n, M (n + 1) ⟶ M n) (u : ∀ n, N (n + 1) ⟶ N n)
    (e : ∀ n, M n ≅ N n) (he : ∀ n, v n ≫ (e n).hom = (e (n + 1)).hom ≫ u n)
    {K : D} (h : IsDerivedLimit v K) : IsDerivedLimit u K := by
  obtain ⟨p, δ, h⟩ := h
  let E := Pi.mapIso e
  have ht : towerTransitionEndomorphism v ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism u :=
    (towerTransitionEndomorphism_natural_backward v u (fun n ↦ (e n).hom)
      (fun n ↦ (he n).symm)).symm
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  exact Pretriangulated.isomorphic_distinguished _ h _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) E.symm E.symm
      (by simp)
      (by
        change towerTransitionEndomorphism u ≫ E.inv =
          E.inv ≫ towerTransitionEndomorphism v
        apply (cancel_mono E.hom).mp
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun t ↦ E.inv ≫ t) ht.symm)
      (by simp))

private theorem exactFunctor_roos
    {D E : Type*} [Category* D] [Category* E]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (F : D ⥤ E) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {M : ℕ → D} [HasProduct M] [HasProduct (fun n ↦ F.obj (M n))]
    (v : ∀ n, M (n + 1) ⟶ M n) {K : D}
    (h : IsDerivedLimit v K) :
    IsDerivedLimit (K := fun n ↦ F.obj (M n)) (fun n ↦ F.map (v n)) (F.obj K) := by
  obtain ⟨p, δ, h⟩ := h
  let e := PreservesProduct.iso F M
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = F.map (Pi.π M n) := by
    simp [e]
  refine ⟨F.map p ≫ e.hom,
    e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  have ht : F.map (towerTransitionEndomorphism v) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (K := fun n ↦ F.obj (M n)) (fun n ↦ F.map (v n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_π, Functor.map_sub]
    rw [← Category.assoc, he, ← F.map_comp]
    rw [← F.map_comp, Pi.lift_π, Category.id_comp, F.map_comp]
  exact Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ h) _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by
        change (F.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map p
        simp)
      (by
        change towerTransitionEndomorphism (K := fun n ↦ F.obj (M n))
          (fun n ↦ F.map (v n)) ≫ e.inv =
          e.inv ≫ F.map (towerTransitionEndomorphism v)
        apply (cancel_mono e.hom).mp
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun t ↦ e.inv ≫ t) ht.symm)
      (by
        change (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
          (shiftFunctor E (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
        simp))

private theorem exactEquivalence_reflects_roos
    {D E : Type*} [Category* D] [Category* E]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    [HasProductsOfShape ℕ D] [HasProductsOfShape ℕ E]
    (F : D ≌ E) [F.functor.Additive] [F.inverse.Additive]
    [F.functor.CommShift ℤ] [F.inverse.CommShift ℤ]
    [F.functor.IsTriangulated] [F.inverse.IsTriangulated]
    {M : ℕ → D} (v : ∀ n, M (n + 1) ⟶ M n) (K : D)
    (h : IsDerivedLimit (K := fun n ↦ F.functor.obj (M n))
      (fun n ↦ F.functor.map (v n)) (F.functor.obj K)) :
    IsDerivedLimit v K := by
  have hh := exactFunctor_roos (M := fun n ↦ F.functor.obj (M n))
    F.inverse (fun n ↦ F.functor.map (v n)) h
  have hc := roos_congr (M := fun n ↦ F.inverse.obj (F.functor.obj (M n)))
    (N := M) (fun n ↦ F.inverse.map (F.functor.map (v n))) v
    (fun n ↦ (F.unitIso.app (M n)).symm) (fun n ↦ by
      exact F.unitIso.inv.naturality (v n)) hh
  obtain ⟨p, δ, hp⟩ := hc
  exact roos_change_vertex v (F.unitIso.app K) p δ hp

set_option backward.isDefEq.respectTransparency false in
private theorem complete_change_representative
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal)
    {K : adicDatumDerived X d}
    (C P : CochainComplex (adicDatumModules X d) ℤ)
    (eC : (completedConstantQ _).obj C ≅ K)
    (eP : (completedConstantQ _).obj P ≅ K)
    (hC : IsCompletedIntrinsicallyDerivedComplete X d r f hf C eC) :
    IsCompletedIntrinsicallyDerivedComplete X d r f hf P eP := by
  obtain ⟨F, η, hη⟩ := completedIntrinsicCompletion_descends X d r f
  obtain ⟨c, hc⟩ := hη C
  obtain ⟨p, hp⟩ := hη P
  have hunit : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex X d r f C)) := by
    have : IsIso (eC.inv ≫ (completedConstantQ _).map
        (completedKoszulUnitComplex X d r f C)) := hC
    exact IsIso.of_isIso_comp_left eC.inv _
  have : IsIso (η.app ((completedConstantQ _).obj C)) := by
    have hcomp : IsIso (η.app ((completedConstantQ _).obj C) ≫ c.hom) := by
      rw [hc]
      exact hunit
    exact IsIso.of_isIso_comp_right _ c.hom
  let e := eC ≪≫ eP.symm
  have he : IsIso (η.app ((completedConstantQ _).obj P)) := by
    have : IsIso (e.hom ≫ η.app ((completedConstantQ _).obj P)) := by
      change IsIso ((𝟭 _).map e.hom ≫ η.app ((completedConstantQ _).obj P))
      rw [η.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  change IsIso (eP.inv ≫ (completedConstantQ _).map
    (completedKoszulUnitComplex X d r f P))
  rw [← hp]
  infer_instance

private def fixedScalar {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A : Type (u + 1)} [CommRing A] (a : A) :
    𝟭 (Sheaf J (ModuleCat.{u + 1} A)) ⟶ 𝟭 (Sheaf J (ModuleCat.{u + 1} A)) where
  app M := a • 𝟙 M
  naturality {_ _} f := by simp

private def fixedDifference {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A : Type (u + 1)} [CommRing A] (a : A) :
    countablePower (Sheaf J (ModuleCat.{u + 1} A)) ⟶
      countablePower (Sheaf J (ModuleCat.{u + 1} A)) where
  app M := towerTransitionEndomorphism (K := fun _ : ℕ ↦ M)
    (fun _ ↦ (fixedScalar J a).app M)
  naturality {_ _} f := towerTransitionEndomorphism_natural_backward _ _ (fun _ ↦ f)
    (fun _ ↦ (fixedScalar J a).naturality f)

private theorem constantSheaf_linear (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).Linear A := by
  infer_instance

private theorem constantScalar_nilpotent (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (M : ModuleCat.{u + 1} A)
    (a : A) (n : ℕ) (hn : ∀ x : M, a ^ n • x = 0) :
    IsNilpotent (show End ((constantSheaf (ProEt.topology X)
      (ModuleCat.{u + 1} A)).obj M) from (fixedScalar (ProEt.topology X) a).app _) := by
  let F := constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)
  let : F.Linear A := constantSheaf_linear X A
  have hz : (a ^ n • 𝟙 M : M ⟶ M) = 0 := by
    ext x
    exact hn x
  refine ⟨n, ?_⟩
  change (a • (1 : End (F.obj M))) ^ n = 0
  rw [smul_pow, one_pow]
  change (a ^ n • 𝟙 (F.obj M) : F.obj M ⟶ F.obj M) = 0
  rw [← F.map_id, ← F.map_smul, hz, F.map_zero]

private theorem constantRestriction_limits
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A : Type (u + 1)} [CommRing A] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (ConstantScalarComparison.restriction J A R α) := by
  let F := ConstantScalarComparison.restriction J A R α
  let V := sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let : PreservesLimitsOfSize.{u + 1, u + 1} (V ⋙ sheafToPresheaf _ _) :=
    show PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})) by infer_instance
  let : PreservesLimitsOfSize.{u + 1, u + 1} V :=
    preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.toSheaf.{u + 1} R ⋙ sheafToPresheaf _ _) :=
    show PreservesLimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) by infer_instance
  let : PreservesLimitsOfSize.{u + 1, u + 1} (SheafOfModules.toSheaf.{u + 1} R) :=
    preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  let e : F ⋙ V ≅ SheafOfModules.toSheaf.{u + 1} R :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let : PreservesLimitsOfSize.{u + 1, u + 1} (F ⋙ V) :=
    preservesLimits_of_natIso e.symm
  exact preservesLimits_of_reflects_of_preserves _ V

private theorem fixedDifference_map
    {B C : Type*} [Category* B] [Category* C]
    [Preadditive B] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A B] [Linear A C]
    [HasCountableProducts B] [HasCountableProducts C]
    (F : B ⥤ C) [F.Linear A] [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] (a : A) (M : B) :
    IsIso (F.map (towerTransitionEndomorphism (K := fun _ : ℕ ↦ M)
      (fun _ ↦ a • 𝟙 M))) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ F.obj M)
        (fun _ ↦ a • 𝟙 (F.obj M))) := by
  simpa only [F.map_smul, F.map_id] using
    ConstantCompletion.tower_map_iso_iff F (fun _ : ℕ ↦ M) (fun _ ↦ a • 𝟙 M)

private def coefficientSections
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {A : Type (max v w)} [CommRing A] (R : Sheaf J CommRingCat.{max v w})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (R.obj ⋙ forget₂ CommRingCat.{max v w} RingCat.{max v w})) :
    A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max v w} RingCat.{max v w}) where
  toFun a := ⟨fun W ↦ α.app W a, fun f ↦ by
    exact (ConcreteCategory.congr_hom (α.naturality f) a).symm⟩
  map_one' := by ext W; exact (α.app W).hom.map_one
  map_mul' a b := by ext W; exact (α.app W).hom.map_mul a b
  map_zero' := by ext W; exact (α.app W).hom.map_zero
  map_add' a b := by ext W; exact (α.app W).hom.map_add a b

@[instance_reducible]
private def coefficientLinear
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {A : Type (max v w)} [CommRing A] (R : Sheaf J CommRingCat.{max v w})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (R.obj ⋙ forget₂ CommRingCat.{max v w} RingCat.{max v w})) :
    Linear A (SheafOfModules.{max v w}
      ((sheafCompose J (forget₂ CommRingCat.{max v w} RingCat.{max v w})).obj R)) :=
  let : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max v w} RingCat.{max v w}))
      (SheafOfModules.{max v w}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (coefficientSections R α)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (coefficientSections R α a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (coefficientSections R α a) g }

private theorem constantRestriction_reflectsIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A : Type (u + 1)} [CommRing A] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj) :
    (ConstantScalarComparison.restriction J A R α).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    let V := sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    have : IsIso ((SheafOfModules.toSheaf R).map f) :=
      V.map_isIso ((ConstantScalarComparison.restriction J A R α).map f)
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

private theorem scalarDifference_on_complex
    {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [HasCountableProducts B] [CountableAB4Star B]
    {A : Type*} [CommRing A] [Linear A B]
    (C : CochainComplex B ℤ) (a : A)
    (hC : ∀ q : ℤ, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ C.X q) (fun _ ↦ a • 𝟙 (C.X q))))
    [HasCountableProducts (DerivedCategory B)] :
    IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ DerivedCategory.Q.obj C)
        (fun _ ↦ a • 𝟙 (DerivedCategory.Q.obj C))) := by
  let : HasCountableProducts (CochainComplex B ℤ) :=
    { out J _ := by
        have : HasLimitsOfShape (Discrete J) B := inferInstance
        infer_instance }
  let Δ := towerTransitionEndomorphism (K := fun _ : ℕ ↦ C) (fun _ ↦ a • 𝟙 C)
  have heval (q : ℤ) : IsIso (Δ.f q) := by
    let E := HomologicalComplex.eval B (.up ℤ) q
    let : E.Linear A := { map_smul := by intros; rfl }
    apply (fixedDifference_map (HomologicalComplex.eval B (.up ℤ) q) a C).mpr
    exact hC q
  have : IsIso Δ := HomologicalComplex.Hom.isIso_of_components Δ
  have hQ (E : ℕ → CochainComplex B ℤ) :
      PreservesLimit (Discrete.functor E) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      (derivedCategory_termwiseProduct_isLimit B ℕ E).some
  let : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := B)) :=
    preservesLimitsOfShape_of_discrete _
  exact (fixedDifference_map DerivedCategory.Q a C).mp (DerivedCategory.Q.map_isIso Δ)

private theorem moduleLimit_sections_ext
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R) (W : X.ProEtᵒᵖ)
    (x y : (limit S).val.obj W)
    (h : ∀ n : ℕ, (limit.π S (op n)).val.app W x =
      (limit.π S (op n)).val.app W y) : x = y := by
  exact Concrete.isLimit_ext _
    (isLimitOfPreserves (SheafOfModules.evaluation R W) (limit.isLimit S)) x y
    (fun n ↦ h n.unop)

private theorem localModel_constantLinearIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (R₀ Rhat : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (Rₙ : ℕ → Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ρ : ∀ n : ℕ, R₀ ⟶ Rₙ n) (π : ∀ n : ℕ, Rhat ⟶ Rₙ n)
    (α₀ : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R₀.obj)
    (αhat : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ Rhat.obj)
    (hα : ∀ n W a, (ρ n).hom.app W (α₀.app W a) =
      (π n).hom.app W (αhat.app W a))
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R₀)
    (F : SheafOfModules.{u + 1} Rhat) (V : X.ProEt)
    (hF : IsAdicLisseLocalModel X R₀ Rhat Rₙ ρ π S F V) :
    Nonempty (((ConstantScalarComparison.restriction (ProEt.topology X) A Rhat αhat).obj
      F).over V ≅
      ((ConstantScalarComparison.restriction (ProEt.topology X) A R₀ α₀).obj
        (limit S)).over V) := by
  obtain ⟨e, he⟩ := hF
  have hs (W : (Over V)ᵒᵖ) (a : A) (x : F.val.obj (op W.unop.left)) :
      e.hom.hom.app W (αhat.app (op W.unop.left) a • x) =
        α₀.app (op W.unop.left) a •
          (show (limit S).val.obj (op W.unop.left) from e.hom.hom.app W x) := by
    apply moduleLimit_sections_ext X R₀ S (op W.unop.left)
    intro n
    rw [he n W _ _ x (hα n _ a)]
    exact ((limit.π S (op n)).val.app (op W.unop.left)).hom.map_smul _ _ |>.symm
  have hl (W : (Over V)ᵒᵖ) (x : F.val.obj (op W.unop.left)) :
      e.inv.hom.app W (e.hom.hom.app W x) = x := by
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun h ↦ h.hom) e.hom_inv_id) W) x
  have hr (W : (Over V)ᵒᵖ) (x : (limit S).val.obj (op W.unop.left)) :
      e.hom.hom.app W (e.inv.hom.app W x) = x := by
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun h ↦ h.hom) e.inv_hom_id) W) x
  let P := ((ConstantScalarComparison.restriction (ProEt.topology X) A Rhat αhat).obj
    F).over V
  let Q := ((ConstantScalarComparison.restriction (ProEt.topology X) A R₀ α₀).obj
    (limit S)).over V
  refine ⟨ObjectProperty.isoMk _ (NatIso.ofComponents (fun W ↦ ?_) ?_)⟩
  · exact (show (P.obj.obj W : Type (u + 1)) ≃ₗ[A] Q.obj.obj W from
      { toFun := fun x ↦ e.hom.hom.app W x
        invFun := fun x ↦ e.inv.hom.app W x
        left_inv := hl W
        right_inv := hr W
        map_add' := fun x y ↦ (e.hom.hom.app W).hom.map_add x y
        map_smul' := hs W }).toModuleIso
  · intro W Z f
    ext x
    exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) x


private def relativeCompletedScalarUnit
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A) :=
  CoefficientSerre.relativeScalarUnit g A ≫
    Functor.whiskerRight ((adicTowerInverseImage g).map (adicDatumScalar X d)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private def relativeCompletedRestriction
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A) :=
  ConstantScalarComparison.restriction (ProEt.topology Y) A
    ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (adicDatumRing X d)))
    (relativeCompletedScalarUnit g d)

@[instance_reducible]
private def relativeCompletedLinear
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A) :=
  coefficientLinear ((adicTowerInverseImage g).obj (adicDatumRing X d))
    (relativeCompletedScalarUnit g d)

private theorem relativeModel_constantLinearIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A)
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicDatumRing X d)))
    (V : Y.ProEt) (N : ModuleCat.{u + 1} A)
    (hF : IsAdicLisseLocalModel Y
      ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (adicLisseConstantRing X A)))
      ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (adicDatumRing X d)))
      (fun n ↦ (adicLisseForget Y).obj
        ((adicTowerInverseImage g).obj ((adicLisseRingSystem X d.ideal).obj (op n))))
      (fun n ↦ (adicLisseForget Y).map ((adicTowerInverseImage g).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))))))
      (fun n ↦ (adicLisseForget Y).map ((adicTowerInverseImage g).map
        (limit.π (adicLisseRingSystem X d.ideal) (op n))))
      (adicLisseModuleSystem X d.ideal N ⋙
        proEtaleModuleInverseImage g (adicLisseConstantRing X A)) F V) :
    Nonempty (((relativeCompletedRestriction g d).obj F).over V ≅
      ((CoefficientSerre.relativeRestriction g A).obj
        (limit (adicLisseModuleSystem X d.ideal N ⋙
          proEtaleModuleInverseImage g (adicLisseConstantRing X A)))).over V) := by
  apply localModel_constantLinearIso Y _ _ _ _ _
    (CoefficientSerre.relativeScalarUnit g A) _ _ _ F V hF
  intro n W a
  let c := (adicLisseForget Y).map ((adicTowerInverseImage g).map (adicDatumScalar X d))
  have hc := congrArg (fun φ ↦ (adicLisseForget Y).map ((adicTowerInverseImage g).map φ))
    ((adicDatumScalar_exists X d).exists.choose_spec n)
  rw [Functor.map_comp, Functor.map_comp] at hc
  exact (ConcreteCategory.congr_hom (congr_app (congrArg (fun h ↦ h.hom) hc) W)
    ((CoefficientSerre.relativeScalarUnit g A).app W a)).symm

private theorem relativeLisse_fixedDifference
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A)
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicDatumRing X d)))
    (hF : @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal F)
    (a : A) (ha : a ∈ d.ideal) :
    IsIso ((fixedDifference (ProEt.topology Y) a).app
      ((relativeCompletedRestriction g d).obj F)) := by
  classical
  obtain ⟨T, hT, hlocal⟩ := hF
  let I := Σ V : Y.ProEt, {f : V ⟶ ⊤_ Y.ProEt // T f}
  let V : I → Y.ProEt := fun v ↦ v.1
  have hcover : (ProEt.topology Y).CoversTop V := by
    apply ((ProEt.topology Y).coversTop_iff_of_isTerminal (⊤_ Y.ProEt)
      terminalIsTerminal V).mpr
    apply (ProEt.topology Y).superset_covering _ hT
    intro W f hf
    exact ⟨⟨W, ⟨f, hf⟩⟩, ⟨𝟙 W⟩⟩
  apply Sheaf.isIso_of_coversTop hcover
  intro v
  let E := (ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) (V v)
  let : E.Additive := { map_add := by intros; ext W x; rfl }
  let : E.Linear A := { map_smul := by intros; ext W x; rfl }
  apply (fixedDifference_map E a _).mpr
  obtain ⟨N, hN, hfin, hmodel⟩ := hlocal (V v) v.2.val v.2.property
  obtain ⟨e⟩ := relativeModel_constantLinearIso g d F (V v) N hmodel
  apply isoLocus_of_iso _ (fixedDifference ((ProEt.topology Y).over (V v)) a) e
  let S := adicLisseModuleSystem X d.ideal N ⋙
    proEtaleModuleInverseImage g (adicLisseConstantRing X A)
  let G := CoefficientSerre.relativeRestriction g A
  let : PreservesLimitsOfSize.{u + 1, u + 1} G :=
    constantRestriction_limits (ProEt.topology Y) _
      (CoefficientSerre.relativeScalarUnit g A)
  let : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink _
  let eL := preservesLimitIso (G ⋙ E) S
  apply isoLocus_of_iso _ (fixedDifference ((ProEt.topology Y).over (V v)) a) eL
  apply isIso_on_limit (S ⋙ G ⋙ E) _ (fixedDifference _ a)
  intro n
  let QN := ModuleCat.of A (N ⧸ (d.ideal ^ (n.unop + 1) • ⊤ : Submodule A N))
  let en := E.mapIso (CoefficientSerre.relativeConstantEncoding g A QN)
  apply isoLocus_of_iso _ (fixedDifference ((ProEt.topology Y).over (V v)) a) en
  apply (fixedDifference_map E a _).mp
  have hn : IsNilpotent (show End
      ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj QN) from
        (fixedScalar (ProEt.topology Y) a).app _) := by
    apply constantScalar_nilpotent Y QN a (n.unop + 1)
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (a ^ (n.unop + 1) • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow ha _) (Submodule.mem_top : x ∈ ⊤)
  have hi : IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ (constantSheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} A)).obj QN) (fun _ ↦ a • 𝟙 _)) :=
    difference_iso_of_nilpotent _ hn
  exact E.map_isIso _

private theorem relativeLisse_scalarDifference
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : ProEtaleAdicCoefficientDatum A)
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicDatumRing X d)))
    (hF : @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal F)
    (a : A) (ha : a ∈ d.ideal) :
    let := relativeCompletedLinear g d
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ F) (fun _ ↦ a • 𝟙 F)) := by
  let := relativeCompletedLinear g d
  let T := relativeCompletedRestriction g d
  let : T.Additive := { map_add := by intros; ext W x; rfl }
  let : T.Linear A := { map_smul := by intros; ext W x; rfl }
  let : PreservesLimitsOfSize.{u + 1, u + 1} T :=
    constantRestriction_limits (ProEt.topology Y)
      ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (adicDatumRing X d)))
      (relativeCompletedScalarUnit g d)
  let : PreservesLimitsOfSize.{0, 0} T := preservesLimitsOfSize_shrink _
  let : T.ReflectsIsomorphisms :=
    constantRestriction_reflectsIso (ProEt.topology Y)
      ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (adicDatumRing X d)))
      (relativeCompletedScalarUnit g d)
  have h : IsIso (T.map (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ F) (fun _ ↦ a • 𝟙 F))) :=
    (fixedDifference_map T a F).mpr (relativeLisse_fixedDifference g d F hF a ha)
  exact isIso_of_reflects_iso _ T

private def coefficientGlobalSection
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {A : Type (max v w)} [CommRing A] (R : Sheaf J CommRingCat.{max v w})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (R.obj ⋙ forget₂ CommRingCat RingCat)) (a : A) :
    (R.obj ⋙ CategoryTheory.forget CommRingCat).sections :=
  ⟨fun W ↦ α.app W a, fun f ↦
    (ConcreteCategory.congr_hom (α.naturality f) a).symm⟩

private theorem coefficient_scalarDerived
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A : Type u} [CommRing A] (R : Sheaf J CommRingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{v} (ConstantCompletion.Mod R)] (a : A)
    (K : DerivedCategory (ConstantCompletion.Mod R)) :
    let := coefficientLinear R α
    (ConstantCompletion.scalarDerived R (coefficientGlobalSection R α a)).app K =
      a • 𝟙 K := by
  let := coefficientLinear R α
  let τ : 𝟭 (DerivedCategory (ConstantCompletion.Mod R)) ⟶ 𝟭 _ :=
    { app := fun K ↦ a • 𝟙 K
      naturality := by intros; simp }
  suffices ConstantCompletion.scalarDerived R (coefficientGlobalSection R α a) = τ by
    exact congrArg (fun η ↦ η.app K) this
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  rw [ConstantCompletion.scalarDerived_fac]
  change DerivedCategory.Q.map _ = a • 𝟙 (DerivedCategory.Q.obj P)
  rw [← DerivedCategory.Q.map_id, ← DerivedCategory.Q.map_smul]
  congr 1

private theorem small_complete_of_scalarDifference
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A : Type u} [CommRing A] (R : Sheaf J CommRingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{v} (ConstantCompletion.Mod R)]
    [∀ U : C, HasDerivedCategory.{v}
      (SheafOfModules.{u} ((siteModuleRings R).over U))]
    [HasCountableProducts (DerivedCategory (ConstantCompletion.Mod R))]
    (I : RingedSiteIdeal R) (r : ℕ) (f : Fin r → A)
    (hs : ∀ U, I.sections U =
      Ideal.span (Set.range (fun i ↦ α.app (op U) (f i))))
    (K : DerivedCategory (ConstantCompletion.Mod R))
    (h : let := coefficientLinear R α
      ∀ i, IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K)
        (fun _ ↦ f i • 𝟙 K))) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion K := by
  let := coefficientLinear R α
  have hc (i : Fin r) (U : C) :
      IsRingedSiteCompleteElement J R K U (α.app (op U) (f i)) := by
    apply (ConstantCompletion.complete_iff_globalTower J R
      (coefficientGlobalSection R α (f i)) K).mpr ?_ U
    simpa only [coefficient_scalarDerived R α] using h i
  intro U x hx
  obtain ⟨S, hS, _, _, _⟩ := ringedSite_complete_elements_ideal J R K
  apply (localCompleteness_models_iff J R K U x).mpr
  apply (hS U x).mp
  have hle : I.sections U ≤ S U := by
    rw [hs]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (hS U _).mpr (hc i U)
  obtain ⟨y, hy⟩ := hx
  apply hle
  change y.val = x at hy
  exact hy ▸ y.property

private def actualScalarUnit
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶
      (pbcAdicCompletion X d).obj ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (adicDatumScalar X (intrinsicPresentationDatum d)).hom ≫
        (pbcCompletedComparison X d).hom.hom) (forget₂ CommRingCat RingCat)

private def cechScalarUnit
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (Functor.const (completedCechSite X)ᵒᵖ).obj (RingCat.of A) ⟶
      (completedCechRing X d).obj ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight (completedCechScalarMap X d) (forget₂ CommRingCat RingCat)

private theorem cechFunctor_linear
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let := coefficientLinear (pbcAdicCompletion X d) (actualScalarUnit X d)
    let := coefficientLinear (completedCechRing X d) (cechScalarUnit X d)
    (completedCechModulesEquiv X d).functor.Linear A := by
  let := coefficientLinear (pbcAdicCompletion X d) (actualScalarUnit X d)
  let := coefficientLinear (completedCechRing X d) (cechScalarUnit X d)
  refine { map_smul := ?_ }
  intro M N φ a
  ext U x
  rfl

private theorem actual_complete_of_scalarDifference
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    [HasCountableProducts (PbcCompletedDerived X d)]
    (h : let := coefficientLinear (pbcAdicCompletion X d) (actualScalarUnit X d)
      ∀ j, IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ DerivedCategory.Q.obj C)
        (fun _ ↦ f j • 𝟙 _))) :
    IsDerivedCompleteIntrinsic X d r f hf (DerivedCategory.Q.obj C) C (Iso.refl _) := by
  let := coefficientLinear (pbcAdicCompletion X d) (actualScalarUnit X d)
  let := coefficientLinear (completedCechRing X d) (cechScalarUnit X d)
  let E := completedCechDerivedEquiv X d
  let : (completedCechModulesEquiv X d).functor.Linear A := cechFunctor_linear X d
  let : E.functor.Linear A := by
    change (completedCechModulesEquiv X d).functor.mapDerivedCategory.Linear A
    infer_instance
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : HasCountableProducts (ringedSiteDerived (completedCechRing X d)) :=
    ⟨fun J _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.inverse⟩
  let : ∀ U : completedCechSite X, HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} ((siteModuleRings (completedCechRing X d)).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : IsNoetherianRing A := d.noetherian
  obtain ⟨β, hβ, _⟩ := completed_constant_coefficient_equivalence X d
  let I := ConstantCompletion.kernelIdeal
    (ConstantCompletion.projection (completedCechTopology X) A d.ideal 0)
  let J := comapIdealIso β I
  have hgen := cech_kernel_generators X d β hβ r f hf
  let : Mono J.inclusion := ideal_inclusion_mono J
  obtain ⟨D, _, _, hD, _⟩ := ringedKoszulCompletionReflector (completedCechRing X d)
    r (fun j ↦ completedCechScalar X d (f j)) J.module J.inclusion hgen
  have hs : ∀ U, J.sections U = Ideal.span (Set.range
      (fun j ↦ (cechScalarUnit X d).app (op U) (f j))) := by
    intro U
    have hj := comapIdealIso_sections_span β I
      (fun j ↦ ConstantCompletion.algebraSection
        (ConstantCompletion.coefficientMap (completedCechTopology X) A d.ideal) (f j))
      (fun V ↦ constant_kernel_generated _ A d.ideal r f hf V) U
    change J.sections U = _ at hj
    rw [hj]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext j
    apply (sectionRingEquiv β (op U)).injective
    change (sectionRingEquiv β (op U))
      ((sectionRingEquiv β (op U)).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    exact (hβ (op U) (f j)).symm
  have hc : IsLocallyDerivedRingedIdealComplete (completedCechRing X d)
      J.module J.inclusion (E.functor.obj (DerivedCategory.Q.obj C)) := by
    apply small_complete_of_scalarDifference (completedCechRing X d) (cechScalarUnit X d)
      J r f hs
    intro _ j
    let := h j
    exact (fixedDifference_map E.functor (f j) (DerivedCategory.Q.obj C)).mp
      (E.functor.map_isIso _)
  have : IsIso (D.unit (E.functor.obj (DerivedCategory.Q.obj C))) := (hD _).mpr hc
  obtain ⟨e, he⟩ := completed_fiber_strict_limit_comparison X d r f C D
  have : IsIso (E.functor.map
      (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r f C))) := by
    apply (isIso_comp_right_iff _ e.hom).mp
    rw [he]
    infer_instance
  change IsIso ((Iso.refl _).inv ≫
    DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r f C))
  simp only [Iso.refl_inv, Category.id_comp]
  exact isIso_of_reflects_iso _ E.functor

private def actualCoefficientScalar
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    adicLisseConstantRing X A ⟶ pbcAdicCompletion X d :=
  adicDatumScalar X (intrinsicPresentationDatum d) ≫ (pbcCompletedComparison X d).hom

private theorem actualCoefficientScalar_projection
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) :
    actualCoefficientScalar X d ≫ pbcAdicProjection X d n =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison X d n).hom := by
  dsimp only [actualCoefficientScalar, pbcCompletedComparison]
  change (adicDatumScalar X (intrinsicPresentationDatum d) ≫
      (HasLimit.isoOfNatIso (pbcConstantSystemComparison X d)).hom) ≫
        limit.π _ (op n) = _
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  erw [(adicDatumScalar_exists X (intrinsicPresentationDatum d)).exists.choose_spec n]
  rfl

private theorem actualCoefficientScalar_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (adicTowerInverseImage g).map (actualCoefficientScalar X d) ≫
        completedCoefficientMap g d =
      (CoefficientSerre.coefficientIso g A).hom ≫ actualCoefficientScalar Y d := by
  let F := adicTowerInverseImage g
  apply limit.hom_ext
  rintro ⟨n⟩
  change (F.map (actualCoefficientScalar X d) ≫ completedCoefficientMap g d) ≫
      pbcAdicProjection Y d n =
    ((CoefficientSerre.coefficientIso g A).hom ≫ actualCoefficientScalar Y d) ≫
      pbcAdicProjection Y d n
  rw [Category.assoc, completedCoefficient_projection, ← F.map_comp_assoc,
    actualCoefficientScalar_projection, F.map_comp]
  simp only [completedFiniteCoefficientMap, Category.assoc]
  change F.map _ ≫ (F.mapIso (pbcLevelConstantComparison X d n)).hom ≫
    (F.mapIso (pbcLevelConstantComparison X d n)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  erw [(proEtaleConstantComparison g).naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))]
  rw [Category.assoc, ← actualCoefficientScalar_projection]
  rfl

private def relativeCoefficientIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (adicTowerInverseImage g).obj (adicDatumRing X (intrinsicPresentationDatum d)) ≅
      pbcAdicCompletion Y d :=
  haveI := completedCoefficient_isIso g d
  (adicTowerInverseImage g).mapIso (pbcCompletedComparison X d) ≪≫
    asIso (completedCoefficientMap g d)

private theorem relativeCoefficientIso_scalar
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    relativeCompletedScalarUnit g (intrinsicPresentationDatum d) ≫
      Functor.whiskerRight (relativeCoefficientIso g d).hom.hom
        (forget₂ CommRingCat RingCat) = actualScalarUnit Y d := by
  have he : (CoefficientSerre.coefficientIso g A).inv ≫
      (adicTowerInverseImage g).map (adicDatumScalar X (intrinsicPresentationDatum d)) ≫
        (relativeCoefficientIso g d).hom = actualCoefficientScalar Y d := by
    dsimp only [relativeCoefficientIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [← (adicTowerInverseImage g).map_comp_assoc]
    change (CoefficientSerre.coefficientIso g A).inv ≫
      (adicTowerInverseImage g).map (actualCoefficientScalar X d) ≫ _ = _
    rw [actualCoefficientScalar_pullback, Iso.inv_hom_id_assoc]
  ext W a
  exact ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.hom.app W) he)
      ((CoefficientSerre.proEtaleModuleScalarUnit Y A).app W a)

private theorem model_complete
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (adicDatumRing X (intrinsicPresentationDatum d)))) ℤ)
    (hC : ∀ q, @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal (C.X q))
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal) :
    let B := pbcRestrict (relativeCoefficientIso g d).inv
    let P := (B.mapHomologicalComplex (.up ℤ)).obj C
    IsDerivedCompleteIntrinsic Y d r f hf (DerivedCategory.Q.obj P) P (Iso.refl _) := by
  let e := relativeCoefficientIso g d
  let B := pbcRestrict e.inv
  let P := (B.mapHomologicalComplex (.up ℤ)).obj C
  let := relativeCompletedLinear g (intrinsicPresentationDatum d)
  let := coefficientLinear (pbcAdicCompletion Y d) (actualScalarUnit Y d)
  let : B.IsEquivalence :=
    (proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso e.symm)).isEquivalence_functor
  let : B.Linear A := by
    refine { map_smul := ?_ }
    intro M N φ a
    ext W x
    have hs := ConcreteCategory.congr_hom
      (congrArg (fun η ↦ η.app W) (relativeCoefficientIso_scalar g d)) a
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun η ↦ η.hom.app W) e.hom_inv_id)
      ((relativeCompletedScalarUnit g (intrinsicPresentationDatum d)).app W a)
    change (relativeCompletedScalarUnit g (intrinsicPresentationDatum d)).app W a •
      φ.val.app W (show M.val.obj W from x) =
        e.inv.hom.app W ((actualScalarUnit Y d).app W a) •
          φ.val.app W (show M.val.obj W from x)
    congr 1
    exact hi.symm.trans (congrArg (fun z ↦ e.inv.hom.app W z) hs)
  let : CountableAB4Star (pbcModules Y (pbcAdicCompletion Y d)) :=
    moduleCountableAB4Star Y _
  let : HasCountableProducts (PbcCompletedDerived Y d) :=
    (derivedCategory_countableProducts_core.{0} _).choose
  apply actual_complete_of_scalarDifference Y d r f hf P
  intro _ j
  apply scalarDifference_on_complex P (f j)
  intro q
  have hj : f j ∈ d.ideal := hf ▸ Ideal.subset_span ⟨j, rfl⟩
  let := relativeLisse_scalarDifference g (intrinsicPresentationDatum d)
    (C.X q) (hC q) (f j) hj
  exact (fixedDifference_map B (f j) (C.X q)).mp (B.map_isIso _)

private theorem actual_unit_of_normalized_unit
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (h : IsIso (DerivedCategory.Q.map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r f
        ((intrinsicPresentationComplex X d).obj C)))) :
    IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r f C)) := by
  let B := intrinsicPresentationModulesBack X d
  let ν := completedKoszulUnitComplex X (intrinsicPresentationDatum d) r f
    ((intrinsicPresentationComplex X d).obj C)
  let e := NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)
  have hn : QuasiIso ν := (DerivedCategory.isIso_Q_map_iff_quasiIso _ ν).mp h
  have hb : QuasiIso ((B.mapHomologicalComplex (.up ℤ)).map ν) := inferInstance
  have he : intrinsicCompletionComplexUnit X d r f C =
      e.hom.app C ≫ (B.mapHomologicalComplex (.up ℤ)).map ν := by
    ext q
    rfl
  rw [he, DerivedCategory.Q.map_comp]
  infer_instance

private theorem actual_towerComplete
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived X d) (hK : PbcIsIntrinsicallyComplete X d K) :
    IsIso (d.completionUnit X K) := by
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  let c := pbcCompletedComparison X d
  let E := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso c)
  let : E.functor.Additive := inferInstanceAs (pbcRestrict c.hom).Additive
  let : E.inverse.Additive := inferInstanceAs (pbcRestrict c.inv).Additive
  let F := intrinsicPresentationModules X d
  let eF : pbcDerivedExtend c.inv ≅ F.mapDerivedCategory :=
    (pbcDerivedScalarAdjunction c.inv).leftAdjointUniq E.mapDerivedCategory.toAdjunction
  let P := DerivedCategory.Q.objPreimage K
  let eP := DerivedCategory.Q.objObjPreimageIso K
  let N := (intrinsicPresentationComplex X d).obj P
  let eN : DerivedCategory.Q.obj N ≅ (pbcDerivedExtend c.inv).obj K :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
      (eF.app K).symm
  have hc := complete_change_representative X (intrinsicPresentationDatum d) r f hf
    C N eC eN hC
  have hn : IsIso (DerivedCategory.Q.map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r f N)) := by
    have : IsIso (eN.inv ≫ DerivedCategory.Q.map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r f N)) := hc
    exact IsIso.of_isIso_comp_left eN.inv _
  have hu := actual_unit_of_normalized_unit X d r f P hn
  let := hu
  have hi : IsDerivedCompleteIntrinsic X d r f hf K P eP := by
    change IsIso (eP.inv ≫ DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit X d r f P))
    infer_instance
  obtain ⟨q, hq⟩ := completedKoszulQuotientComparison X d r f hf K P eP
  change intrinsicCompletionUnit X d r f hf K P eP ≫ q.hom = d.completionUnit X K at hq
  rw [← hq]
  let : IsIso (intrinsicCompletionUnit X d r f hf K P eP) := hi
  infer_instance

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

private def ordinaryRestrictionInverseImageIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcRestrict φ ⋙ proEtaleRingModulePullback g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ≅
      proEtaleRingModulePullback g S ((adicTowerInverseImage g).obj S) (Iso.refl _) ⋙
        pbcRestrict ((adicTowerInverseImage g).map φ) := by
  let h := proEtaleRingRestrictionPullbackInv_isIso g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    φ ((adicTowerInverseImage g).map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact asIso (proEtaleRingRestrictionPullbackInv g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    φ ((adicTowerInverseImage g).map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm))

private theorem ordinaryRestrictionInverseImage_unit
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (N : pbcModules X S) :
    let G := adicTowerInverseImage g
    let aR := proEtaleRingModuleAdjunction g R (G.obj R) (Iso.refl _)
    let aS := proEtaleRingModuleAdjunction g S (G.obj S) (Iso.refl _)
    aR.unit.app ((pbcRestrict φ).obj N) ≫
        (proEtaleRingModuleDirectImage g R (G.obj R) (Iso.refl _)).map
          ((ordinaryRestrictionInverseImageIso g φ).hom.app N) =
      (pbcRestrict φ).map (aS.unit.app N) ≫
        (proEtaleRingRestrictionDirectImage g R S (G.obj R) (G.obj S) φ (G.map φ)
          (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans (Category.comp_id _).symm)).hom.app
          ((proEtaleRingModulePullback g S (G.obj S) (Iso.refl _)).obj N) := by
  let G := adicTowerInverseImage g
  let aR := proEtaleRingModuleAdjunction g R (G.obj R) (Iso.refl _)
  let aS := proEtaleRingModuleAdjunction g S (G.obj S) (Iso.refl _)
  let t := (pbcRestrict φ).map (aS.unit.app N) ≫
    (proEtaleRingRestrictionDirectImage g R S (G.obj R) (G.obj S)
      φ (G.map φ) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).hom.app
        ((proEtaleRingModulePullback g S (G.obj S) (Iso.refl _)).obj N)
  have ht := (aR.homEquiv _ _).apply_symm_apply t
  rw [Adjunction.homEquiv_unit] at ht
  have hm : (aR.homEquiv _ _).symm t =
      (ordinaryRestrictionInverseImageIso g φ).hom.app N := by
    rw [Adjunction.homEquiv_counit]
    dsimp only [ordinaryRestrictionInverseImageIso, asIso_hom,
      proEtaleRingRestrictionPullbackInv, proEtaleRingRestrictionPullbackApp]
    dsimp only [t]
    rw [Functor.map_comp, Category.assoc]
  rw [hm] at ht
  exact ht

attribute [local irreducible] ordinaryRestrictionInverseImageIso

private theorem inverseImage_coherence
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    (Rφ : B ⥤ A) (Rψ : C ⥤ B) (Rχ : C ⥤ A)
    (Sφ : B' ⥤ A') (Sψ : C' ⥤ B') (Sχ : C' ⥤ A')
    (FA : A ⥤ A') (FB : B ⥤ B') (FC : C ⥤ C')
    (PA : A' ⥤ A) (PB : B' ⥤ B) (PC : C' ⥤ C)
    (adjA : FA ⊣ PA) (adjB : FB ⊣ PB) (adjC : FC ⊣ PC)
    (r : Rψ ⋙ Rφ ≅ Rχ) (r' : Sψ ⋙ Sφ ≅ Sχ)
    (a : Rφ ⋙ FA ≅ FB ⋙ Sφ) (b : Rψ ⋙ FB ≅ FC ⋙ Sψ)
    (z : Rχ ⋙ FA ≅ FC ⋙ Sχ)
    (dφ : PB ⋙ Rφ ≅ Sφ ⋙ PA) (dψ : PC ⋙ Rψ ≅ Sψ ⋙ PB)
    (dχ : PC ⋙ Rχ ≅ Sχ ⋙ PA)
    (ha : ∀ N, adjA.unit.app (Rφ.obj N) ≫ PA.map (a.hom.app N) =
      Rφ.map (adjB.unit.app N) ≫ dφ.hom.app (FB.obj N))
    (hb : ∀ N, adjB.unit.app (Rψ.obj N) ≫ PB.map (b.hom.app N) =
      Rψ.map (adjC.unit.app N) ≫ dψ.hom.app (FC.obj N))
    (hz : ∀ N, adjA.unit.app (Rχ.obj N) ≫ PA.map (z.hom.app N) =
      Rχ.map (adjC.unit.app N) ≫ dχ.hom.app (FC.obj N))
    (N : C)
    (hd : r.hom.app (PC.obj (FC.obj N)) ≫ dχ.hom.app (FC.obj N) =
      Rφ.map (dψ.hom.app (FC.obj N)) ≫
        dφ.hom.app (Sψ.obj (FC.obj N)) ≫ PA.map (r'.hom.app (FC.obj N))) :
    FA.map (r.hom.app N) ≫ z.hom.app N =
      a.hom.app (Rψ.obj N) ≫ Sφ.map (b.hom.app N) ≫ r'.hom.app (FC.obj N) := by
  apply (adjA.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hrn := adjA.unit.naturality (r.hom.app N)
  dsimp only [Functor.id_map, Functor.comp_map] at hrn
  erw [← Category.assoc, ← hrn, Category.assoc, hz]
  erw [reassoc_of% ha]
  erw [← dφ.hom.naturality_assoc (b.hom.app N)]
  erw [← Rφ.map_comp_assoc, hb]
  simp only [Functor.map_comp, Category.assoc]
  erw [← r.hom.naturality_assoc (adjC.unit.app N)]
  erw [hd]
  rfl

private theorem ordinaryDirectImage_coherence
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules Y ((adicTowerInverseImage g).obj B)) :
  let G := adicTowerInverseImage g
  let P (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModuleDirectImage g R (G.obj R) (Iso.refl _)
  let r := pbcRestrictComp φ ψ χ h
  let r' := pbcRestrictComp (G.map φ) (G.map ψ) (G.map χ)
    ((G.map_comp _ _).symm.trans (congrArg G.map h))
  let dφ := proEtaleRingRestrictionDirectImage g R S (G.obj R) (G.obj S)
    φ (G.map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dψ := proEtaleRingRestrictionDirectImage g S B (G.obj S) (G.obj B)
    ψ (G.map ψ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dχ := proEtaleRingRestrictionDirectImage g R B (G.obj R) (G.obj B)
    χ (G.map χ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  r.hom.app ((P B).obj M) ≫ dχ.hom.app M =
    (pbcRestrict φ).map (dψ.hom.app M) ≫
      dφ.hom.app ((pbcRestrict (G.map ψ)).obj M) ≫
      (P R).map (r'.hom.app M) := by
  let G := adicTowerInverseImage g
  let P (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModuleDirectImage g R (G.obj R) (Iso.refl _)
  let r := pbcRestrictComp φ ψ χ h
  let r' := pbcRestrictComp (G.map φ) (G.map ψ) (G.map χ)
    ((G.map_comp _ _).symm.trans (congrArg G.map h))
  let dφ := proEtaleRingRestrictionDirectImage g R S (G.obj R) (G.obj S)
    φ (G.map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dψ := proEtaleRingRestrictionDirectImage g S B (G.obj S) (G.obj B)
    ψ (G.map ψ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dχ := proEtaleRingRestrictionDirectImage g R B (G.obj R) (G.obj B)
    χ (G.map χ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hr := (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec
  have hr' := (pbcRestrictComp_exists (G.map φ) (G.map ψ) (G.map χ)
    ((G.map_comp _ _).symm.trans (congrArg G.map h))).exists.choose_spec
  have hdφ := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g R S
    (G.obj R) (G.obj S) φ (G.map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm))).1
  have hdψ := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g S B
    (G.obj S) (G.obj B) ψ (G.map ψ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm))).1
  have hdχ := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g R B
    (G.obj R) (G.obj B) χ (G.map χ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm))).1
  ext W x
  change (dχ.hom.app _).val.app W ((r.hom.app _).val.app W x) =
    (r'.hom.app _).val.app ((proEtaleBaseChange g).op.obj W)
      ((dφ.hom.app ((pbcRestrict (G.map ψ)).obj M)).val.app W
        ((dψ.hom.app M).val.app W x))
  erw [hr, hdχ, hdψ, hdφ, hr']

private theorem ordinaryRestrictionInverseImageIso_comp
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (N : pbcModules X B) :
    let G := adicTowerInverseImage g
    let F (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
      proEtaleRingModulePullback g R (G.obj R) (Iso.refl _)
    (F R).map ((pbcRestrictComp φ ψ χ h).hom.app N) ≫
        (ordinaryRestrictionInverseImageIso g χ).hom.app N =
      (ordinaryRestrictionInverseImageIso g φ).hom.app ((pbcRestrict ψ).obj N) ≫
        (pbcRestrict (G.map φ)).map
          ((ordinaryRestrictionInverseImageIso g ψ).hom.app N) ≫
        (pbcRestrictComp (G.map φ) (G.map ψ) (G.map χ)
          ((G.map_comp _ _).symm.trans (congrArg G.map h))).hom.app ((F B).obj N) := by
  let G := adicTowerInverseImage g
  let F (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModulePullback g R (G.obj R) (Iso.refl _)
  let P (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModuleDirectImage g R (G.obj R) (Iso.refl _)
  let adj (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : F R ⊣ P R :=
    proEtaleRingModuleAdjunction g R (G.obj R) (Iso.refl _)
  let r := pbcRestrictComp φ ψ χ h
  let r' := pbcRestrictComp (G.map φ) (G.map ψ) (G.map χ)
    ((G.map_comp _ _).symm.trans (congrArg G.map h))
  let dφ := proEtaleRingRestrictionDirectImage g R S (G.obj R) (G.obj S)
    φ (G.map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dψ := proEtaleRingRestrictionDirectImage g S B (G.obj S) (G.obj B)
    ψ (G.map ψ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let dχ := proEtaleRingRestrictionDirectImage g R B (G.obj R) (G.obj B)
    χ (G.map χ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact inverseImage_coherence (pbcRestrict φ) (pbcRestrict ψ) (pbcRestrict χ)
    (pbcRestrict (G.map φ)) (pbcRestrict (G.map ψ)) (pbcRestrict (G.map χ))
    (F R) (F S) (F B) (P R) (P S) (P B) (adj R) (adj S) (adj B) r r'
    (ordinaryRestrictionInverseImageIso g φ) (ordinaryRestrictionInverseImageIso g ψ)
    (ordinaryRestrictionInverseImageIso g χ) dφ dψ dχ
    (ordinaryRestrictionInverseImage_unit g φ) (ordinaryRestrictionInverseImage_unit g ψ)
    (ordinaryRestrictionInverseImage_unit g χ) N
    (ordinaryDirectImage_coherence g φ ψ χ h ((F B).obj N))

private abbrev localUnderlyingReduction
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ) (n : ℕ) :=
  (pbcDerivedRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
    (adicTowerLocalReduction d g C n)

private def localUnderlyingStep
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (b a : ℕ) (hab : a ≤ b) :
    localUnderlyingReduction g d C b ⟶ localUnderlyingReduction g d C a :=
  (pbcDerivedRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d b))).map
      (adicTowerLocalTransition d g C b a hab) ≫
    (pbcDerivedRestrictComp
      ((adicTowerInverseImage g).map (pbcAdicProjection X d b))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d b a hab))
      ((adicTowerInverseImage g).map (pbcAdicProjection X d a))
      (((adicTowerInverseImage g).map_comp _ _).symm.trans
        (congrArg (adicTowerInverseImage g).map
          (pbcAdicProjection_comp X d b a hab)))).hom.app
      (adicTowerLocalReduction d g C a)

private def restrictionInverseImageIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedRestrict φ ⋙ adicTowerPullback g R ≅
      adicTowerPullback g S ⋙ pbcDerivedRestrict ((adicTowerInverseImage g).map φ) :=
  (proEtaleRingRestrictionDerivedPullback g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    φ ((adicTowerInverseImage g).map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)).symm

private def derivedCompositionComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫ Functor.mapDerivedCategoryNatIso e

private theorem complexCompIso_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P =
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro q
  simp

private theorem derivedCompositionComparison_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    (derivedCompositionComparison F G H e).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac F G P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P =
      𝟙 _ := rfl
  have hqi : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P) =
      𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  rw [hqi] at hc
  erw [Category.comp_id] at hc
  dsimp only [derivedCompositionComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc, ← hc]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc, Category.assoc]
  rw [complexCompIso_hom]

private def derivedSquareComparison
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
    (s : G ⋙ L' ≅ L ⋙ H) :
    G.mapDerivedCategory ⋙ L'.mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso G L').symm ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H

private theorem derivedSquareComparison_fac
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
    (s : G ⋙ L' ≅ L ⋙ H) (P : CochainComplex A ℤ) :
    (derivedSquareComparison L L' G H s).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac L H P
  have h₂ := Functor.mapDerivedCategoryCompIso_fac G L' P
  have h₃ := Functor.mapDerivedCategoryNatIso_fac s P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app P =
      𝟙 _ := rfl
  have hi' : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app P =
      𝟙 _ := rfl
  have hqi : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app P) =
      𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  rw [hqi] at h₁
  erw [Category.comp_id] at h₁
  have hqi' : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app P) =
      𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  rw [hqi'] at h₂
  erw [Category.comp_id] at h₂
  dsimp only [derivedSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [h₁, h₃, ← h₂]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem restrictionInverseImageIso_eq
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    restrictionInverseImageIso g φ =
      derivedSquareComparison
        (proEtaleRingModulePullback g S ((adicTowerInverseImage g).obj S) (Iso.refl _))
        (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _))
        (pbcRestrict φ) (pbcRestrict ((adicTowerInverseImage g).map φ))
        (ordinaryRestrictionInverseImageIso g φ) := by
  apply Iso.ext
  simp only [restrictionInverseImageIso, proEtaleRingRestrictionDerivedPullback,
    derivedSquareComparison, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom,
    ordinaryRestrictionInverseImageIso, Category.assoc]
  rfl

attribute [local irreducible] derivedSquareComparison

private theorem derivedSquare_coherence
    {A0 A1 A2 B0 B1 B2 : Type*}
    [Category A0] [Category A1] [Category A2]
    [Category B0] [Category B1] [Category B2]
    [Abelian A0] [Abelian A1] [Abelian A2]
    [Abelian B0] [Abelian B1] [Abelian B2]
    [HasDerivedCategory A0] [HasDerivedCategory A1] [HasDerivedCategory A2]
    [HasDerivedCategory B0] [HasDerivedCategory B1] [HasDerivedCategory B2]
    (Rφ : A1 ⥤ A0) (Rψ : A2 ⥤ A1) (Rχ : A2 ⥤ A0)
    (Sφ : B1 ⥤ B0) (Sψ : B2 ⥤ B1) (Sχ : B2 ⥤ B0)
    (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
    [Rφ.Additive] [PreservesFiniteLimits Rφ] [PreservesFiniteColimits Rφ]
    [Rψ.Additive] [PreservesFiniteLimits Rψ] [PreservesFiniteColimits Rψ]
    [Rχ.Additive] [PreservesFiniteLimits Rχ] [PreservesFiniteColimits Rχ]
    [Sφ.Additive] [PreservesFiniteLimits Sφ] [PreservesFiniteColimits Sφ]
    [Sψ.Additive] [PreservesFiniteLimits Sψ] [PreservesFiniteColimits Sψ]
    [Sχ.Additive] [PreservesFiniteLimits Sχ] [PreservesFiniteColimits Sχ]
    [F0.Additive] [PreservesFiniteLimits F0] [PreservesFiniteColimits F0]
    [F1.Additive] [PreservesFiniteLimits F1] [PreservesFiniteColimits F1]
    [F2.Additive] [PreservesFiniteLimits F2] [PreservesFiniteColimits F2]
    (c : Rψ ⋙ Rφ ≅ Rχ) (c' : Sψ ⋙ Sφ ≅ Sχ)
    (a : Rφ ⋙ F0 ≅ F1 ⋙ Sφ) (b : Rψ ⋙ F1 ≅ F2 ⋙ Sψ)
    (z : Rχ ⋙ F0 ≅ F2 ⋙ Sχ)
    (ho : ∀ N, F0.map (c.hom.app N) ≫ z.hom.app N =
      a.hom.app (Rψ.obj N) ≫ Sφ.map (b.hom.app N) ≫ c'.hom.app (F2.obj N))
    (N : DerivedCategory A2) :
    F0.mapDerivedCategory.map ((derivedCompositionComparison Rψ Rφ Rχ c).hom.app N) ≫
        (derivedSquareComparison F2 F0 Rχ Sχ z).hom.app N =
      (derivedSquareComparison F1 F0 Rφ Sφ a).hom.app (Rψ.mapDerivedCategory.obj N) ≫
        Sφ.mapDerivedCategory.map ((derivedSquareComparison F2 F1 Rψ Sψ b).hom.app N) ≫
        (derivedCompositionComparison Sψ Sφ Sχ c').hom.app (F2.mapDerivedCategory.obj N) := by
  let A := derivedSquareComparison F1 F0 Rφ Sφ a
  let Bτ := derivedSquareComparison F2 F1 Rψ Sψ b
  let Z := derivedSquareComparison F2 F0 Rχ Sχ z
  let C := derivedCompositionComparison Rψ Rφ Rχ c
  let D := derivedCompositionComparison Sψ Sφ Sχ c'
  let η : Rψ.mapDerivedCategory ⋙ Rφ.mapDerivedCategory ⋙ F0.mapDerivedCategory ⟶
      F2.mapDerivedCategory ⋙ Sχ.mapDerivedCategory :=
    Functor.whiskerRight C.hom F0.mapDerivedCategory ≫ Z.hom
  let θ : Rψ.mapDerivedCategory ⋙ Rφ.mapDerivedCategory ⋙ F0.mapDerivedCategory ⟶
      F2.mapDerivedCategory ⋙ Sχ.mapDerivedCategory :=
    Functor.whiskerLeft Rψ.mapDerivedCategory A.hom ≫
      Functor.whiskerRight Bτ.hom Sφ.mapDerivedCategory ≫
      Functor.whiskerLeft F2.mapDerivedCategory D.hom
  have hc : η = θ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro P
    let TP := (Rψ.mapHomologicalComplex (.up ℤ)).obj P
    let FP := (F2.mapHomologicalComplex (.up ℤ)).obj P
    let s := F0.mapDerivedCategory.map
        (Rφ.mapDerivedCategory.map (Rψ.mapDerivedCategoryFactors.hom.app P)) ≫
      F0.mapDerivedCategory.map (Rφ.mapDerivedCategoryFactors.hom.app TP) ≫
      F0.mapDerivedCategoryFactors.hom.app
        ((Rφ.mapHomologicalComplex (.up ℤ)).obj TP)
    let t := Sχ.mapDerivedCategory.map (F2.mapDerivedCategoryFactors.hom.app P) ≫
      Sχ.mapDerivedCategoryFactors.hom.app FP
    let cP : (Rφ.mapHomologicalComplex (.up ℤ)).obj TP ⟶
        (Rχ.mapHomologicalComplex (.up ℤ)).obj P :=
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P
    let zP : (F0.mapHomologicalComplex (.up ℤ)).obj
        ((Rχ.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        (Sχ.mapHomologicalComplex (.up ℤ)).obj FP :=
      (NatTrans.mapHomologicalComplex z.hom (.up ℤ)).app P
    let aP : (F0.mapHomologicalComplex (.up ℤ)).obj
        ((Rφ.mapHomologicalComplex (.up ℤ)).obj TP) ⟶
        (Sφ.mapHomologicalComplex (.up ℤ)).obj
          ((F1.mapHomologicalComplex (.up ℤ)).obj TP) :=
      (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app TP
    let bP : (F1.mapHomologicalComplex (.up ℤ)).obj TP ⟶
        (Sψ.mapHomologicalComplex (.up ℤ)).obj FP :=
      (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app P
    let dP : (Sφ.mapHomologicalComplex (.up ℤ)).obj
        ((Sψ.mapHomologicalComplex (.up ℤ)).obj FP) ⟶
        (Sχ.mapHomologicalComplex (.up ℤ)).obj FP :=
      (NatTrans.mapHomologicalComplex c'.hom (.up ℤ)).app FP
    let u := (F0.mapHomologicalComplex (.up ℤ)).map cP ≫ zP
    let v := aP ≫ (Sφ.mapHomologicalComplex (.up ℤ)).map bP ≫ dP
    have huv : u = v := by
      apply HomologicalComplex.hom_ext
      intro q
      exact ho (P.X q)
    have hl : η.app (DerivedCategory.Q.obj P) ≫ t = s ≫ DerivedCategory.Q.map u := by
      have hz := derivedSquareComparison_fac F2 F0 Rχ Sχ z P
      have hc := derivedCompositionComparison_fac Rψ Rφ Rχ c P
      have hn := F0.mapDerivedCategoryFactors.hom.naturality
        ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P)
      dsimp only [Functor.comp_map] at hn
      dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, t]
      simp only [Category.assoc]
      erw [hz]
      erw [← F0.mapDerivedCategory.map_comp_assoc, hc]
      simp only [Functor.map_comp, Category.assoc]
      erw [reassoc_of% hn]
      simp only [s, u, cP, zP, Functor.map_comp, Category.assoc]
      rfl
    have hr : θ.app (DerivedCategory.Q.obj P) ≫ t = s ≫ DerivedCategory.Q.map v := by
      have hd := derivedCompositionComparison_fac Sψ Sφ Sχ c' FP
      have hb := derivedSquareComparison_fac F2 F1 Rψ Sψ b P
      have ha := derivedSquareComparison_fac F1 F0 Rφ Sφ a TP
      have hnD := D.hom.naturality (F2.mapDerivedCategoryFactors.hom.app P)
      have hnA := A.hom.naturality (Rψ.mapDerivedCategoryFactors.hom.app P)
      have hnS := Sφ.mapDerivedCategoryFactors.hom.naturality
        ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app P)
      dsimp only [Functor.comp_map] at hnD hnA hnS
      dsimp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, t, s, v]
      simp only [Category.assoc]
      erw [← reassoc_of% hnD, hd]
      erw [← Sφ.mapDerivedCategory.map_comp_assoc,
        ← Sφ.mapDerivedCategory.map_comp_assoc]
      simp only [Category.assoc]
      erw [hb]
      simp only [Functor.map_comp, Category.assoc]
      erw [← reassoc_of% hnA]
      erw [reassoc_of% hnS]
      erw [reassoc_of% ha]
      rw [complexCompIso_hom]
    apply (cancel_mono t).mp
    rw [hl, hr, huv]
  have hN := congrArg (fun τ ↦ τ.app N) hc
  exact hN

private theorem restrictionInverseImageIso_comp
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (N : DerivedCategory (pbcModules X B)) :
    (adicTowerPullback g R).map ((pbcDerivedRestrictComp φ ψ χ h).hom.app N) ≫
        (restrictionInverseImageIso g χ).hom.app N =
      (restrictionInverseImageIso g φ).hom.app ((pbcDerivedRestrict ψ).obj N) ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map φ)).map
          ((restrictionInverseImageIso g ψ).hom.app N) ≫
        (pbcDerivedRestrictComp ((adicTowerInverseImage g).map φ)
          ((adicTowerInverseImage g).map ψ) ((adicTowerInverseImage g).map χ)
          (((adicTowerInverseImage g).map_comp _ _).symm.trans
            (congrArg (adicTowerInverseImage g).map h))).hom.app
          ((adicTowerPullback g B).obj N) := by
  let G := adicTowerInverseImage g
  let F (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModulePullback g R (G.obj R) (Iso.refl _)
  let Rφ := pbcRestrict φ
  let Rψ := pbcRestrict ψ
  let Rχ := pbcRestrict χ
  let Sφ := pbcRestrict (G.map φ)
  let Sψ := pbcRestrict (G.map ψ)
  let Sχ := pbcRestrict (G.map χ)
  let c := pbcRestrictComp φ ψ χ h
  let c' := pbcRestrictComp (G.map φ) (G.map ψ) (G.map χ)
    ((G.map_comp _ _).symm.trans (congrArg G.map h))
  let a := ordinaryRestrictionInverseImageIso g φ
  let b := ordinaryRestrictionInverseImageIso g ψ
  let z := ordinaryRestrictionInverseImageIso g χ
  have hcoh := derivedSquare_coherence Rφ Rψ Rχ Sφ Sψ Sχ (F R) (F S) (F B)
    c c' a b z (ordinaryRestrictionInverseImageIso_comp g φ ψ χ h) N
  have hc : derivedCompositionComparison Rψ Rφ Rχ c =
      pbcDerivedRestrictComp φ ψ χ h := rfl
  have hd : derivedCompositionComparison Sψ Sφ Sχ c' =
      pbcDerivedRestrictComp (G.map φ) (G.map ψ) (G.map χ)
        ((G.map_comp _ _).symm.trans (congrArg G.map h)) := rfl
  have ha : derivedSquareComparison (F S) (F R) Rφ Sφ a =
      restrictionInverseImageIso g φ := (restrictionInverseImageIso_eq g φ).symm
  have hb : derivedSquareComparison (F B) (F S) Rψ Sψ b =
      restrictionInverseImageIso g ψ := (restrictionInverseImageIso_eq g ψ).symm
  have hz : derivedSquareComparison (F B) (F R) Rχ Sχ z =
      restrictionInverseImageIso g χ := (restrictionInverseImageIso_eq g χ).symm
  rw [hc, hd, ha, hb, hz] at hcoh
  exact hcoh


private def ordinaryScalarStep
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) :
    pbcExtend φ ⟶ pbcExtend χ ⋙ pbcRestrict ψ :=
  let k : 𝟭 (pbcModules Y R) ⟶ (pbcExtend χ ⋙ pbcRestrict ψ) ⋙ pbcRestrict φ :=
    (pbcScalarAdjunction χ).unit ≫
      Functor.whiskerLeft (pbcExtend χ) (pbcRestrictComp φ ψ χ h).inv
  { app M := ((pbcScalarAdjunction φ).homEquiv M _).symm (k.app M)
    naturality := by
      intro M N f
      apply ((pbcScalarAdjunction φ).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
        Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      exact k.naturality f }

private def ordinaryUnderlyingStep
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) :
    pbcExtend φ ⋙ pbcRestrict φ ⟶ pbcExtend χ ⋙ pbcRestrict χ :=
  Functor.whiskerRight (ordinaryScalarStep φ ψ χ h) (pbcRestrict φ) ≫
    Functor.whiskerLeft (pbcExtend χ) (pbcRestrictComp φ ψ χ h).hom

private def scalarStepComplex
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y R) ℤ) :
    ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (ordinaryScalarStep φ ψ χ h) (.up ℤ)).app P

private def underlyingStepComplex
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y R) ℤ) :
    ((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((pbcRestrict χ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (ordinaryUnderlyingStep φ ψ χ h) (.up ℤ)).app P

private theorem ordinaryUnderlyingStep_unit
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules Y R) :
    (pbcScalarAdjunction φ).unit.app M ≫ (ordinaryUnderlyingStep φ ψ χ h).app M =
      (pbcScalarAdjunction χ).unit.app M := by
  have ht := ((pbcScalarAdjunction φ).homEquiv M _).apply_symm_apply
    ((pbcScalarAdjunction χ).unit.app M ≫
      (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj M))
  rw [Adjunction.homEquiv_unit] at ht
  dsimp only [ordinaryUnderlyingStep, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have ht' : (pbcScalarAdjunction φ).unit.app M ≫
      (pbcRestrict φ).map ((ordinaryScalarStep φ ψ χ h).app M) =
      (pbcScalarAdjunction χ).unit.app M ≫
        (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj M) := ht
  rw [← Category.assoc, ht']
  simp

private theorem derivedRestrictComp_inv_fac
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).inv.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcRestrict χ).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (pbcRestrictComp φ ψ χ h) (.up ℤ)).inv.app P) := by
  have hc := derivedCompositionComparison_fac (pbcRestrict ψ) (pbcRestrict φ)
    (pbcRestrict χ) (pbcRestrictComp φ ψ χ h) P
  apply (cancel_epi ((pbcDerivedRestrictComp φ ψ χ h).hom.app
    (DerivedCategory.Q.obj P))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  erw [← Category.assoc, hc]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp,
    Iso.hom_inv_id_app]
  have hqid := (DerivedCategory.Q : CochainComplex (pbcModules Y R) ℤ ⥤
    DerivedCategory (pbcModules Y R)).map_id
      ((((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)) ⋙
        ((pbcRestrict φ).mapHomologicalComplex (.up ℤ))).obj P)
  erw [hqid, Category.comp_id]
  rfl

private theorem scalarStep_complexCounit
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict ψ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict ψ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      pbcComplexCounit φ P ≫ DerivedCategory.Q.map
        (scalarStepComplex φ ψ χ h P) := by
  let PC := ((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P
  let q : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj PC :=
    scalarStepComplex φ ψ χ h P
  have ht := ((pbcDerivedScalarAdjunction φ).homEquiv _ _).apply_symm_apply
    ((pbcDerivedScalarAdjunction χ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrictComp φ ψ χ h).inv.app
        ((pbcDerivedExtend χ).obj (DerivedCategory.Q.obj P)))
  erw [Adjunction.homEquiv_unit] at ht
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality (pbcComplexCounit χ P)
  dsimp only [Functor.comp_map] at hn
  have hq := (pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hq
  have ho :
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P ≫
        ((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map q =
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction χ).unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (pbcRestrictComp φ ψ χ h) (.up ℤ)).inv.app PC := by
    apply HomologicalComplex.hom_ext
    intro i
    exact ((pbcScalarAdjunction φ).homEquiv (P.X i) _).apply_symm_apply _
  have ht' : (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map
        (pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P)) =
      (pbcDerivedScalarAdjunction χ).unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrictComp φ ψ χ h).inv.app
          ((pbcDerivedExtend χ).obj (DerivedCategory.Q.obj P)) := ht
  apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
  apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app
    (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj PC))).mp
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [← Category.assoc, ← Category.assoc, ht']
  simp only [Category.assoc]
  erw [← reassoc_of% hn]
  erw [derivedRestrictComp_inv_fac]
  erw [reassoc_of% (pbcDerivedScalarAdjunction_exists χ).exists.choose_spec P hP]
  erw [hq]
  erw [reassoc_of% (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P hP]
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ho]

private def coefficientEquivalence
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ S) : pbcModules Y R ≌ pbcModules Y S :=
  proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso e.symm)

private instance coefficientEquivalence_additive
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ S) : (coefficientEquivalence Y e).functor.Additive :=
  inferInstanceAs (pbcRestrict e.inv).Additive

private instance coefficientEquivalence_inverse_additive
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ S) : (coefficientEquivalence Y e).inverse.Additive :=
  inferInstanceAs (pbcRestrict e.hom).Additive

private theorem coefficientEquivalence_reflects_roos
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ S)
    [HasCountableProducts (DerivedCategory (pbcModules Y R))]
    [HasCountableProducts (DerivedCategory (pbcModules Y S))]
    {M : ℕ → DerivedCategory (pbcModules Y R)}
    (v : ∀ n, M (n + 1) ⟶ M n) (K : DerivedCategory (pbcModules Y R))
    (h : IsDerivedLimit (K := fun n ↦
      (coefficientEquivalence Y e).functor.mapDerivedCategory.obj (M n))
      (fun n ↦ (coefficientEquivalence Y e).functor.mapDerivedCategory.map (v n))
      ((coefficientEquivalence Y e).functor.mapDerivedCategory.obj K)) :
    IsDerivedLimit v K := by
  let E := coefficientEquivalence Y e
  let : E.mapDerivedCategory.functor.Additive :=
    inferInstanceAs E.functor.mapDerivedCategory.Additive
  let : E.mapDerivedCategory.inverse.Additive :=
    inferInstanceAs E.inverse.mapDerivedCategory.Additive
  let : E.mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs (E.functor.mapDerivedCategory.CommShift ℤ)
  let : E.mapDerivedCategory.inverse.CommShift ℤ :=
    inferInstanceAs (E.inverse.mapDerivedCategory.CommShift ℤ)
  let : E.mapDerivedCategory.functor.IsTriangulated :=
    inferInstanceAs E.functor.mapDerivedCategory.IsTriangulated
  let : E.mapDerivedCategory.inverse.IsTriangulated :=
    inferInstanceAs E.inverse.mapDerivedCategory.IsTriangulated
  exact exactEquivalence_reflects_roos E.mapDerivedCategory v K h

private def coefficientReductionIso
    (Y : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (en : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : e.hom ≫ φ' = φ ≫ en.hom) :
    (pbcExtend φ ⋙ pbcRestrict φ) ⋙ (coefficientEquivalence Y e).functor ≅
      (coefficientEquivalence Y e).functor ⋙ (pbcExtend φ' ⋙ pbcRestrict φ') :=
  reductionTransport (coefficientEquivalence Y e) (coefficientEquivalence Y en)
    (pbcExtend φ) (pbcRestrict φ) (pbcExtend φ') (pbcRestrict φ')
    (pbcScalarAdjunction φ) (pbcScalarAdjunction φ')
    ((pbcRestrictComp φ en.hom (φ ≫ en.hom) rfl) ≪≫
      (pbcRestrictComp e.hom φ' (φ ≫ en.hom) h).symm)

private theorem coefficientReductionIso_unit
    (Y : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (en : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : e.hom ≫ φ' = φ ≫ en.hom) (M : pbcModules Y R) :
    (coefficientEquivalence Y e).functor.map ((pbcScalarAdjunction φ).unit.app M) ≫
        (coefficientReductionIso Y e en φ φ' h).hom.app M =
      (pbcScalarAdjunction φ').unit.app ((coefficientEquivalence Y e).functor.obj M) :=
  reductionTransport_unit _ _ _ _ _ _ _ _ _ M

private theorem scalarUnit_epi
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (hφ : ∀ U, Function.Surjective (φ.hom.app U))
    (M : pbcModules Y R) : Epi ((pbcScalarAdjunction φ).unit.app M) := by
  have ha : pbcScalarAdjunction φ = comparisonChangeAdjunction Y φ := by
    apply (pbcScalarAdjunction_exists φ).unique
      (pbcScalarAdjunction_exists φ).exists.choose_spec
    intro N V x
    exact comparisonChangeUnit_apply Y φ N V x
  rw [ha]
  exact comparisonChangeUnit_epi Y φ hφ M

private theorem coefficientReductionIso_step
    (Y : Scheme.{u}) {R S B R' S' B' :
      Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (es : S ≅ S') (eb : B ≅ B')
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (φ' : R' ⟶ S') (ψ' : S' ⟶ B') (χ' : R' ⟶ B') (h' : φ' ≫ ψ' = χ')
    (hs : e.hom ≫ φ' = φ ≫ es.hom) (hb : e.hom ≫ χ' = χ ≫ eb.hom)
    (hφ : ∀ U, Function.Surjective (φ.hom.app U)) (M : pbcModules Y R) :
    (coefficientEquivalence Y e).functor.map ((ordinaryUnderlyingStep φ ψ χ h).app M) ≫
        (coefficientReductionIso Y e eb χ χ' hb).hom.app M =
      (coefficientReductionIso Y e es φ φ' hs).hom.app M ≫
        (ordinaryUnderlyingStep φ' ψ' χ' h').app
          ((coefficientEquivalence Y e).functor.obj M) := by
  let E := (coefficientEquivalence Y e).functor
  let := scalarUnit_epi Y φ hφ M
  apply (cancel_epi (E.map ((pbcScalarAdjunction φ).unit.app M))).mp
  rw [← E.map_comp_assoc, ordinaryUnderlyingStep_unit, coefficientReductionIso_unit]
  rw [← Category.assoc, coefficientReductionIso_unit, ordinaryUnderlyingStep_unit]

private def derivedScalarStep
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) :
    pbcDerivedExtend φ ⟶ pbcDerivedExtend χ ⋙ pbcDerivedRestrict ψ :=
  let k : 𝟭 (DerivedCategory (pbcModules Y R)) ⟶
      (pbcDerivedExtend χ ⋙ pbcDerivedRestrict ψ) ⋙ pbcDerivedRestrict φ :=
    (pbcDerivedScalarAdjunction χ).unit ≫
      Functor.whiskerLeft (pbcDerivedExtend χ) (pbcDerivedRestrictComp φ ψ χ h).inv
  { app M := ((pbcDerivedScalarAdjunction φ).homEquiv M _).symm (k.app M)
    naturality := by
      intro M N f
      apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
        Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      exact k.naturality f }

private def derivedUnderlyingStep
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) :
    pbcDerivedExtend φ ⋙ pbcDerivedRestrict φ ⟶
      pbcDerivedExtend χ ⋙ pbcDerivedRestrict χ :=
  Functor.whiskerRight (derivedScalarStep φ ψ χ h) (pbcDerivedRestrict φ) ≫
    Functor.whiskerLeft (pbcDerivedExtend χ) (pbcDerivedRestrictComp φ ψ χ h).hom

private theorem underlyingStep_complexCounit
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    (derivedUnderlyingStep φ ψ χ h).app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict χ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (underlyingStepComplex φ ψ χ h P) := by
  let PC := ((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P
  let q : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj PC :=
    (NatTrans.mapHomologicalComplex (ordinaryScalarStep φ ψ χ h) (.up ℤ)).app P
  have hn := (pbcDerivedRestrictComp φ ψ χ h).hom.naturality (pbcComplexCounit χ P)
  dsimp only [Functor.comp_map] at hn
  have hc := derivedCompositionComparison_fac (pbcRestrict ψ) (pbcRestrict φ)
    (pbcRestrict χ) (pbcRestrictComp φ ψ χ h) PC
  have hq := (pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hq
  dsimp only [derivedUnderlyingStep, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  have happ : (derivedScalarStep φ ψ χ h).app (DerivedCategory.Q.obj P) =
      pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P) := rfl
  rw [happ]
  simp only [Category.assoc]
  erw [← reassoc_of% hn, hc]
  erw [← (pbcDerivedRestrict φ).map_comp_assoc,
    ← (pbcDerivedRestrict φ).map_comp_assoc]
  simp only [Category.assoc]
  erw [scalarStep_complexCounit φ ψ χ h P hP]
  erw [Functor.map_comp, Category.assoc, reassoc_of% hq]
  simp only [← DerivedCategory.Q.map_comp]
  congr 2

private theorem reconstruction_complexCounit_isIso
    {Y : Scheme.{u}} {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (pbcComplexCounit φ P) := by
  have := pbcExtensionCounit_isIso φ P hP
  dsimp only [pbcComplexCounit]
  infer_instance

private def reductionComplexComparison
    {Y : Scheme.{u}} {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    (pbcDerivedRestrict φ).obj ((pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)) :=
  haveI := reconstruction_complexCounit_isIso φ P hP
  (pbcDerivedRestrict φ).mapIso (asIso (pbcComplexCounit φ P)) ≪≫
    (pbcRestrict φ).mapDerivedCategoryFactors.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)

private theorem reductionComplexComparison_step
    {Y : Scheme.{u}} {R S B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    (derivedUnderlyingStep φ ψ χ h).app (DerivedCategory.Q.obj P) ≫
        (reductionComplexComparison χ P hP).hom =
      (reductionComplexComparison φ P hP).hom ≫ DerivedCategory.Q.map
        (underlyingStepComplex φ ψ χ h P) :=
  by
    simpa only [reductionComplexComparison, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, Iso.app_hom, Category.assoc] using underlyingStep_complexCounit φ ψ χ h P hP

attribute [local irreducible] reductionComplexComparison

private def coefficientReductionComplexIso
    (Y : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (en : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : e.hom ≫ φ' = φ ≫ en.hom) (P : CochainComplex (pbcModules Y R) ℤ) :
    (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj
      (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P))) ≅
      ((pbcRestrict φ').mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend φ').mapHomologicalComplex (.up ℤ)).obj
          (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P)) :=
  (NatIso.mapHomologicalComplex (coefficientReductionIso Y e en φ φ' h) (.up ℤ)).app P

private def coefficientDerivedReductionIso
    (Y : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (en : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : e.hom ≫ φ' = φ ≫ en.hom)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hEP : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    (coefficientEquivalence Y e).functor.mapDerivedCategory.obj
        ((pbcDerivedRestrict φ).obj ((pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P))) ≅
      (pbcDerivedRestrict φ').obj ((pbcDerivedExtend φ').obj (DerivedCategory.Q.obj
        (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P))) :=
  let E := (coefficientEquivalence Y e).functor
  E.mapDerivedCategory.mapIso (reductionComplexComparison φ P hP) ≪≫
    E.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      (coefficientReductionComplexIso Y e en φ φ' h P) ≪≫
    (reductionComplexComparison φ' ((E.mapHomologicalComplex (.up ℤ)).obj P) hEP).symm

private theorem coefficientDerivedReductionIso_normalized
    (Y : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (en : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (h : e.hom ≫ φ' = φ ≫ en.hom)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hEP : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    let E := (coefficientEquivalence Y e).functor
    (coefficientDerivedReductionIso Y e en φ φ' h P hP hEP).hom ≫
        (reductionComplexComparison φ' ((E.mapHomologicalComplex (.up ℤ)).obj P) hEP).hom =
      E.mapDerivedCategory.map (reductionComplexComparison φ P hP).hom ≫
        E.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map
          (coefficientReductionComplexIso Y e en φ φ' h P).hom := by
  simp [coefficientDerivedReductionIso, Category.assoc]

attribute [local irreducible] coefficientDerivedReductionIso

private theorem coefficientDerivedReductionIso_step
    (Y : Scheme.{u}) {R S B R' S' B' :
      Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ R') (es : S ≅ S') (eb : B ≅ B')
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (φ' : R' ⟶ S') (ψ' : S' ⟶ B') (χ' : R' ⟶ B') (h' : φ' ≫ ψ' = χ')
    (hs : e.hom ≫ φ' = φ ≫ es.hom) (hb : e.hom ≫ χ' = χ ≫ eb.hom)
    (hφ : ∀ U, Function.Surjective (φ.hom.app U))
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hEP : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    let E := (coefficientEquivalence Y e).functor
    E.mapDerivedCategory.map
        ((derivedUnderlyingStep φ ψ χ h).app (DerivedCategory.Q.obj P)) ≫
        (coefficientDerivedReductionIso Y e eb χ χ' hb P hP hEP).hom =
      (coefficientDerivedReductionIso Y e es φ φ' hs P hP hEP).hom ≫
        (derivedUnderlyingStep φ' ψ' χ' h').app
          (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E := (coefficientEquivalence Y e).functor
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let q : ((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((pbcRestrict χ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) :=
    underlyingStepComplex φ ψ χ h P
  have hn := E.mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  have ho : (E.mapHomologicalComplex (.up ℤ)).map q ≫
      (coefficientReductionComplexIso Y e eb χ χ' hb P).hom =
    (coefficientReductionComplexIso Y e es φ φ' hs P).hom ≫
      underlyingStepComplex φ' ψ' χ' h' EP := by
    apply HomologicalComplex.hom_ext
    intro i
    exact coefficientReductionIso_step Y e es eb φ ψ χ h φ' ψ' χ' h' hs hb hφ (P.X i)
  apply (cancel_mono (reductionComplexComparison χ' EP hEP).hom).mp
  simp only [Category.assoc]
  rw [coefficientDerivedReductionIso_normalized]
  rw [reductionComplexComparison_step]
  rw [← E.mapDerivedCategory.map_comp_assoc, reductionComplexComparison_step]
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]
  rw [reassoc_of% (coefficientDerivedReductionIso_normalized Y e es φ φ' hs P hP hEP)]
  simp only [← DerivedCategory.Q.map_comp]
  rw [ho]

private def suppliedReductionIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d) {a b : ℤ}
    (L : AdicTowerLocalModel d g M a b) (n : ℕ) :
    (adicTowerPullback g (pbcAdicCompletion X d)).obj
        ((pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj M.tower) ≅
      localUnderlyingReduction g d L.complex n :=
  (adicTowerPullback g (pbcAdicCompletion X d)).mapIso (M.evaluation n).symm ≪≫
    (restrictionInverseImageIso g (pbcAdicProjection X d n)).app (M.level n) ≪≫
    (pbcDerivedRestrict ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).mapIso
      (L.identification n)

private theorem suppliedReductionIso_step
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d) {a b : ℤ}
    (L : AdicTowerLocalModel d g M a b) (j k : ℕ) (hjk : k ≤ j) :
    (adicTowerPullback g (pbcAdicCompletion X d)).map
        ((pbcTowerTransition X (pbcAdicCompletion X d) j k hjk).app M.tower) ≫
        (suppliedReductionIso g d M L k).hom =
      (suppliedReductionIso g d M L j).hom ≫
        localUnderlyingStep g d L.complex j k hjk := by
  let F := adicTowerPullback g (pbcAdicCompletion X d)
  let G := adicTowerInverseImage g
  let R (n : ℕ) := pbcDerivedRestrict (G.map (pbcAdicProjection X d n))
  let e (n : ℕ) := restrictionInverseImageIso g (pbcAdicProjection X d n)
  let s := adicTowerSemilinearTransition X d M.level M.normalization j k hjk
  let c := pbcDerivedRestrictComp (pbcAdicProjection X d j)
    (pbcAdicQuotient X d j k hjk) (pbcAdicProjection X d k)
    (pbcAdicProjection_comp X d j k hjk)
  let c' := pbcDerivedRestrictComp (G.map (pbcAdicProjection X d j))
    (G.map (pbcAdicQuotient X d j k hjk)) (G.map (pbcAdicProjection X d k))
    ((G.map_comp _ _).symm.trans
      (congrArg G.map (pbcAdicProjection_comp X d j k hjk)))
  have ht : (pbcTowerTransition X (pbcAdicCompletion X d) j k hjk).app M.tower ≫
      (M.evaluation k).inv = (M.evaluation j).inv ≫
        (pbcDerivedRestrict (pbcAdicProjection X d j)).map s ≫ c.hom.app (M.level k) := by
    apply (cancel_epi (M.evaluation j).hom).mp
    rw [← Category.assoc, ← M.transition j k hjk]
    dsimp only [c, s]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have htF := congrArg F.map ht
  simp only [Functor.map_comp] at htF
  have hc := restrictionInverseImageIso_comp g (pbcAdicProjection X d j)
    (pbcAdicQuotient X d j k hjk) (pbcAdicProjection X d k)
    (pbcAdicProjection_comp X d j k hjk) (M.level k)
  have hn := (e j).hom.naturality s
  have hn' := c'.hom.naturality (L.identification k).hom
  have hl := congrArg (R j).map (L.compatible j k hjk)
  dsimp only [Functor.comp_map] at hn hn'
  dsimp only [suppliedReductionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    localUnderlyingStep]
  simp only [Category.assoc]
  change F.map _ ≫ F.map (M.evaluation k).inv ≫ (e k).hom.app _ ≫
      (R k).map (L.identification k).hom =
    F.map (M.evaluation j).inv ≫ (e j).hom.app _ ≫ (R j).map
      (L.identification j).hom ≫ (R j).map
      (adicTowerLocalTransition d g L.complex j k hjk) ≫
      c'.hom.app (adicTowerLocalReduction d g L.complex k)
  rw [← Category.assoc, htF]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  rw [reassoc_of% hn]
  rw [← hn']
  simp only [Functor.map_comp, Category.assoc, adicTowerRestrictedTransition] at hl
  simpa only [restrictionInverseImageIso, Iso.symm_hom, Category.assoc] using
    congrArg (fun t ↦ F.map (M.evaluation j).inv ≫ (e j).hom.app (M.level j) ≫ t ≫
      c'.hom.app (adicTowerLocalReduction d g L.complex k)) hl

private theorem coefficientEquivalence_kFlat
    (Y : Scheme.{u}) {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : R ≅ S) (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ q : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      (((coefficientEquivalence Y e).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  let E := coefficientEquivalence Y e
  let σ : pbcExtend e.hom ≅ E.functor :=
    (pbcScalarAdjunction e.hom).leftAdjointUniq E.toAdjunction
  have hk := reductionChange_isKFlat Y e.hom P hP hflat
  let := SheafOfModules.monoidalCategory S
  intro F hF i
  let t := (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj F).mapIso ((NatIso.mapHomologicalComplex σ (.up ℤ)).app P)
  exact (hk F hF i).of_iso (HomologicalComplex₂.total.mapIso t (.up ℤ))

private def completionUnitNat
    (Y : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    𝟭 (PbcCompletedDerived Y d) ⟶ completedReductionTower Y d ⋙
      completedRlim Y (pbcAdicCompletion Y d) :=
  (constLimAdj :
    (Functor.const ℕᵒᵖ : pbcModules Y (pbcAdicCompletion Y d) ⥤ _)
      ⊣ completedTowerLimit Y
        (pbcAdicCompletion Y d)).mapDerivedCategoryRightDerivedAdjunction.unit ≫
    Functor.whiskerRight (completedReductionTowerUnit d Y)
      (completedRlim Y (pbcAdicCompletion Y d))

private theorem model_actual_unit
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (hC : ∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcCompletedComparison X d).hom)).obj (C.X q)))
    (P : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (s : P ⟶ C) [QuasiIso s] :
    let := completedCoefficient_isIso g d
    let E := coefficientEquivalence Y (asIso (completedCoefficientMap g d))
    IsIso (d.completionUnit Y (DerivedCategory.Q.obj
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj P))) := by
  let := completedCoefficient_isIso g d
  let G := adicTowerInverseImage g
  let c := asIso (completedCoefficientMap g d)
  let E := coefficientEquivalence Y c
  let S := pbcRestrict (G.map (pbcCompletedComparison X d).hom)
  let B := pbcRestrict (relativeCoefficientIso g d).inv
  let N := (S.mapHomologicalComplex (.up ℤ)).obj C
  let Q := (B.mapHomologicalComplex (.up ℤ)).obj N
  obtain ⟨r, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  have hQ := model_complete g d N hC r f hf
  obtain ⟨q, hq⟩ := completedKoszulQuotientComparison Y d r f hf
    (DerivedCategory.Q.obj Q) Q (Iso.refl _)
  have hu : IsIso (d.completionUnit Y (DerivedCategory.Q.obj Q)) := by
    change intrinsicCompletionUnit Y d r f hf _ Q (Iso.refl _) ≫ q.hom =
      d.completionUnit Y (DerivedCategory.Q.obj Q) at hq
    rw [← hq]
    let : IsIso (intrinsicCompletionUnit Y d r f hf _ Q (Iso.refl _)) := hQ
    infer_instance
  have hc : (relativeCoefficientIso g d).inv ≫ G.map (pbcCompletedComparison X d).hom =
      c.inv := by
    dsimp only [relativeCoefficientIso, Iso.trans_inv, Functor.mapIso_inv, c, asIso_inv]
    rw [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id]
  let ec : S ⋙ B ≅ E.functor :=
    pbcRestrictComp (relativeCoefficientIso g d).inv
      (G.map (pbcCompletedComparison X d).hom) c.inv hc
  let e : Q ≅ ((E.functor.mapHomologicalComplex (.up ℤ)).obj C) :=
    (NatIso.mapHomologicalComplex ec (.up ℤ)).app C
  let qP := (E.functor.mapHomologicalComplex (.up ℤ)).obj P
  let eqP : DerivedCategory.Q.obj qP ≅ DerivedCategory.Q.obj Q :=
    asIso (DerivedCategory.Q.map ((E.functor.mapHomologicalComplex (.up ℤ)).map s)) ≪≫
      DerivedCategory.Q.mapIso e.symm
  let η := completionUnitNat Y d
  have hn := η.naturality eqP.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have ht : IsIso (η.app (DerivedCategory.Q.obj qP) ≫
      (completedRlim Y (pbcAdicCompletion Y d)).map
        ((completedReductionTower Y d).map eqP.hom)) := by
    rw [← hn]
    let : IsIso (η.app (DerivedCategory.Q.obj Q)) := hu
    infer_instance
  let := ht
  change IsIso (η.app (DerivedCategory.Q.obj qP))
  exact IsIso.of_isIso_comp_right (η.app (DerivedCategory.Q.obj qP))
    ((completedRlim Y (pbcAdicCompletion Y d)).map
      ((completedReductionTower Y d).map eqP.hom))

private theorem canonicalUnderlying_isDerivedLimit
    (Y : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    [HasCountableProducts (PbcCompletedDerived Y d)]
    (K : PbcCompletedDerived Y d) (hu : IsIso (d.completionUnit Y K)) :
    IsDerivedLimit (K := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection Y d n)).obj
      ((pbcDerivedExtend (pbcAdicProjection Y d n)).obj K))
      (fun n ↦ (derivedUnderlyingStep (pbcAdicProjection Y d (n + 1))
      (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection Y d n)
      (pbcAdicProjection_comp Y d (n + 1) n (Nat.le_succ n))).app K) K := by
  let M := pbcReductionAdicTower Y d K
  let T := (completedReductionTower Y d).obj K
  let := hu
  obtain ⟨δ, hδ⟩ := completedRlim_roos Y d T
  have hlim : IsDerivedLimit (completedTowerDerivedStep Y d T) K :=
    roos_change_vertex _ (asIso (d.completionUnit Y K)) _ δ hδ
  apply roos_congr (completedTowerDerivedStep Y d T) _
    (fun n ↦ (M.evaluation n).symm) _ hlim
  intro n
  let j := n + 1
  let φ := pbcAdicProjection Y d j
  let ψ := pbcAdicQuotient Y d j n (Nat.le_succ n)
  let χ := pbcAdicProjection Y d n
  let h := pbcAdicProjection_comp Y d j n (Nat.le_succ n)
  have hs : adicTowerSemilinearTransition Y d M.level M.normalization j n
      (Nat.le_succ n) = pbcReductionTransition φ ψ χ h K := by
    change (pbcDerivedScalarAdjunction ψ).unit.app ((pbcDerivedExtend φ).obj K) ≫
      (pbcDerivedRestrict ψ).map (pbcReductionNormalizationHom φ ψ χ h K) = _
    exact ((pbcDerivedScalarAdjunction ψ).homEquiv _ _).apply_symm_apply _
  have ht := M.transition j n (Nat.le_succ n)
  rw [hs] at ht
  have ht' : (derivedUnderlyingStep φ ψ χ h).app K ≫ (M.evaluation n).hom =
      (M.evaluation j).hom ≫ completedTowerDerivedStep Y d T n := by
    change ((pbcDerivedRestrict φ).map (pbcReductionTransition φ ψ χ h K) ≫
      (pbcDerivedRestrictComp φ ψ χ h).hom.app ((pbcDerivedExtend χ).obj K)) ≫
        (M.evaluation n).hom = _
    rw [Category.assoc]
    exact ht
  apply (cancel_mono (M.evaluation n).hom).mp
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
  erw [ht', Iso.inv_hom_id_assoc]

private def localFiniteCoefficientIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)) ≅
      (pbcAdicRings Y d).obj (op n) :=
  asIso (completedFiniteCoefficientMap g d n)

private theorem localProjection_surjective
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (W : Y.ProEtᵒᵖ) :
    Function.Surjective (((adicTowerInverseImage g).map (pbcAdicProjection X d n)).hom.app W) := by
  let := completedCoefficient_isIso g d
  let e := asIso (completedCoefficientMap g d)
  let en := localFiniteCoefficientIso g d n
  let φ := (adicTowerInverseImage g).map (pbcAdicProjection X d n)
  have hf : φ = e.hom ≫ pbcAdicProjection Y d n ≫ en.inv := by
    dsimp only [e, asIso_hom]
    rw [← Category.assoc, completedCoefficient_projection]
    simp [φ, en, localFiniteCoefficientIso]
  rw [show (adicTowerInverseImage g).map (pbcAdicProjection X d n) = φ from rfl, hf]
  exact (ConcreteCategory.bijective_of_isIso (en.inv.hom.app W)).surjective.comp
    ((completedProjection_surjective Y d n W).comp
      (ConcreteCategory.bijective_of_isIso (e.hom.hom.app W)).surjective)

private theorem suppliedModel_isDerivedLimit
    {X Y : Scheme.{u}} (g : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules Y
      ((adicTowerInverseImage g).obj (pbcAdicCompletion X d))) ℤ)
    (hC : ∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ g A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage g).map
        (pbcCompletedComparison X d).hom)).obj (C.X q))) :
    IsDerivedLimit (fun n ↦ localUnderlyingStep g d C (n + 1) n (Nat.le_succ n))
      (DerivedCategory.Q.obj C) := by
  classical
  let R := (adicTowerInverseImage g).obj (pbcAdicCompletion X d)
  let R' := pbcAdicCompletion Y d
  let G := adicTowerInverseImage g
  let : CountableAB4Star (pbcModules Y R) := moduleCountableAB4Star Y R
  let : CountableAB4Star (pbcModules Y R') := moduleCountableAB4Star Y R'
  let : HasCountableProducts (DerivedCategory (pbcModules Y R)) :=
    (derivedCategory_countableProducts_core.{0} (pbcModules Y R)).choose
  let : HasCountableProducts (DerivedCategory (pbcModules Y R')) :=
    (derivedCategory_countableProducts_core.{0} (pbcModules Y R')).choose
  obtain ⟨P, s, hP, hflat, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) C
  let : QuasiIso s := hs
  let := completedCoefficient_isIso g d
  let e := asIso (completedCoefficientMap g d)
  let E := coefficientEquivalence Y e
  let EP := (E.functor.mapHomologicalComplex (.up ℤ)).obj P
  have hEP := coefficientEquivalence_kFlat Y e P hP hflat
  have hu := model_actual_unit g d C hC P s
  have hactual := canonicalUnderlying_isDerivedLimit Y d (DerivedCategory.Q.obj EP) hu
  let σ (n : ℕ) := G.map (pbcAdicProjection X d n)
  let π (n : ℕ) := pbcAdicProjection Y d n
  let v (n : ℕ) : localUnderlyingReduction g d P (n + 1) ⟶
      localUnderlyingReduction g d P n :=
    localUnderlyingStep g d P (n + 1) n (Nat.le_succ n)
  let W (n : ℕ) := (pbcDerivedRestrict (π n)).obj
    ((pbcDerivedExtend (π n)).obj (DerivedCategory.Q.obj EP))
  let w (n : ℕ) : W (n + 1) ⟶ W n := (derivedUnderlyingStep (π (n + 1))
    (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n)) (π n)
    (pbcAdicProjection_comp Y d (n + 1) n (Nat.le_succ n))).app
      (DerivedCategory.Q.obj EP)
  let V (n : ℕ) := E.functor.mapDerivedCategory.obj (localUnderlyingReduction g d P n)
  let a (n : ℕ) : V n ≅ W n :=
    coefficientDerivedReductionIso Y e (localFiniteCoefficientIso g d n)
      (σ n) (π n) (completedCoefficient_projection g d n) P hP hEP
  have ha (n : ℕ) : E.functor.mapDerivedCategory.map (v n) ≫ (a n).hom =
      (a (n + 1)).hom ≫ w n :=
    coefficientDerivedReductionIso_step Y e (localFiniteCoefficientIso g d (n + 1))
      (localFiniteCoefficientIso g d n)
      (σ (n + 1)) (G.map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) (σ n)
      ((G.map_comp _ _).symm.trans
        (congrArg G.map (pbcAdicProjection_comp X d (n + 1) n (Nat.le_succ n))))
      (π (n + 1)) (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n)) (π n)
      (pbcAdicProjection_comp Y d (n + 1) n (Nat.le_succ n))
      (completedCoefficient_projection g d (n + 1)) (completedCoefficient_projection g d n)
      (localProjection_surjective g d (n + 1)) P hP hEP
  have hai (n : ℕ) : w n ≫ (a n).inv =
      (a (n + 1)).inv ≫ E.functor.mapDerivedCategory.map (v n) := by
    apply (Iso.eq_inv_comp (a (n + 1))).2
    simpa only [Category.assoc] using (Iso.comp_inv_eq (a n)).2 (ha n).symm
  obtain ⟨p, δ, hp⟩ := hactual
  let eP : E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj EP := E.functor.mapDerivedCategoryFactors.app P
  have hvertex : IsDerivedLimit (K := W) w
      (E.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) :=
    roos_change_vertex (M := W) w eP p δ hp
  have hF := roos_congr (M := W) (N := V)
    w (fun n ↦ E.functor.mapDerivedCategory.map (v n))
    (fun n ↦ (a n).symm) hai hvertex
  have hlim := coefficientEquivalence_reflects_roos Y e
    (M := fun n ↦ localUnderlyingReduction g d P n) v
    (DerivedCategory.Q.obj P) hF
  let q := asIso (DerivedCategory.Q.map s)
  let es (n : ℕ) : localUnderlyingReduction g d P n ≅
      localUnderlyingReduction g d C n :=
    (pbcDerivedExtend (σ n) ⋙ pbcDerivedRestrict (σ n)).mapIso q
  have hnat (n : ℕ) : v n ≫ (es n).hom = (es (n + 1)).hom ≫
      localUnderlyingStep g d C (n + 1) n (Nat.le_succ n) := by
    exact (derivedUnderlyingStep (σ (n + 1))
      (G.map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) (σ n)
      ((G.map_comp _ _).symm.trans
        (congrArg G.map (pbcAdicProjection_comp X d (n + 1) n (Nat.le_succ n))))).naturality
          q.hom |>.symm
  have hc := roos_congr (M := fun n ↦ localUnderlyingReduction g d P n)
    (N := fun n ↦ localUnderlyingReduction g d C n) v
    (fun n ↦ localUnderlyingStep g d C (n + 1) n (Nat.le_succ n)) es hnat hlim
  obtain ⟨p, δ, hp⟩ := hc
  exact roos_change_vertex (M := fun n ↦ localUnderlyingReduction g d C n)
    _ q.symm p δ hp

/-- Compatible reductions identify a supplied bounded adic-lisse complex with the
restriction of the intrinsically complete object.

Source: blueprint integral truncations, proof steps 9--10; Stacks Project,
proetale.tex Tags 099Q (1), (4), (5), 099M; algebraization.tex Tag 099I
(blueprint: lem-weil-pbc-supplied-model-reconstruction).

Proof: immersion inverse image preserves small limits, and weakly etale inverse
image is slice restriction. Their composite is exact and preserves countable
products. Exact countable products in pro-etale module categories imply that the
induced derived inverse image also preserves countable products. Consequently it
carries the ambient completion Roos triangle to a Roos triangle for the sequence
of restricted reductions, with vertex the restricted ambient object.

Each term of the supplied model is locally a limit of modules annihilated by
successive powers of the coefficient ideal. For each element a of that ideal,
the endomorphism 1-aT of a countable product is invertible: at each finite torsion
level its inverse is the finite geometric sum, and these inverses are compatible.
This property descends from the supplied local covers, holds termwise for the
complex, and passes through the constant/completed coefficient equivalence. The
Koszul criterion and the unit-compatible Koszul/quotient comparison therefore
show that the model's actual quotient completion unit is invertible.

Take a K-flat resolution with flat terms to compute the model's reductions. The
coefficient-ring comparison is an isomorphism, compatible with every finite
quotient. Uniqueness of the ordinary extension/restriction adjunction transpose,
and its unit compatibility, show that the ordinary quotient comparisons commute
with transition maps. Derived counits transport these equations to the K-flat
resolution. Its canonical completion Roos triangle, transported through the
coefficient equivalence, thus exhibits the model as a derived inverse limit of
its reduction sequence. The supplied identifications and their normalization
equations identify that sequence with the restricted ambient reduction sequence.
Conjugating 1-T by the product of the levelwise isomorphisms identifies their
Roos triangles. Uniqueness up to isomorphism of derived inverse limits now gives
the required isomorphism. This does not choose a lift of the levelwise maps to a
map of strict derived towers. Empty schemes and zero or unit ideals use the same
triangles and units, without any nonzero hypothesis. -/
theorem pbc_suppliedModel_reconstruction
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i] (U : Y.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived X d) (hK : PbcIsIntrinsicallyComplete X d K)
    (a b : ℤ)
    (L : AdicTowerLocalModel d (U.hom ≫ i) (pbcReductionAdicTower X d K) a b) :
    Nonempty (DerivedCategory.Q.obj L.complex ≅
      (adicTowerPullback (U.hom ≫ i) (pbcAdicCompletion X d)).obj K) := by
  classical
  let g := U.hom ≫ i
  let R := pbcAdicCompletion X d
  let R' := (adicTowerInverseImage g).obj R
  let F := adicTowerPullback g R
  let M := pbcReductionAdicTower X d K
  let : CountableAB4Star (pbcModules X R) := moduleCountableAB4Star X R
  let : CountableAB4Star (pbcModules U.left R') := moduleCountableAB4Star U.left R'
  let : HasCountableProducts (DerivedCategory (pbcModules X R)) :=
    (derivedCategory_countableProducts_core.{0} (pbcModules X R)).choose
  let : HasCountableProducts (DerivedCategory (pbcModules U.left R')) :=
    (derivedCategory_countableProducts_core.{0} (pbcModules U.left R')).choose
  let T := (completedReductionTower X d).obj K
  have hu : IsIso (d.completionUnit X K) := actual_towerComplete X d K hK
  obtain ⟨δ, hδ⟩ := completedRlim_roos X d T
  have hlim : IsDerivedLimit (completedTowerDerivedStep X d T) K :=
    roos_change_vertex _ (asIso (d.completionUnit X K)) _ δ hδ
  let : PreservesLimitsOfShape (Discrete ℕ) F :=
    restrictedDerivedInverseImageProducts i U R
  have hFK := exactFunctor_roos F (completedTowerDerivedStep X d T) hlim
  have hL := suppliedModel_isDerivedLimit g d L.complex L.adicLisse
  let an := fun n : ℕ ↦ suppliedReductionIso g d M L n
  have ha (n : ℕ) : F.map (completedTowerDerivedStep X d T n) ≫ (an n).hom =
      (an (n + 1)).hom ≫ localUnderlyingStep g d L.complex (n + 1) n (Nat.le_succ n) :=
    suppliedReductionIso_step g d M L (n + 1) n (Nat.le_succ n)
  have hKL := roos_congr (fun n ↦ F.map (completedTowerDerivedStep X d T n))
    (fun n ↦ localUnderlyingStep g d L.complex (n + 1) n (Nat.le_succ n)) an ha hFK
  exact (exists_isDerivedLimit_and_iso _
    (fun n ↦ localUnderlyingStep g d L.complex (n + 1) n (Nat.le_succ n))).2 _ _ hL hKL

end AlgebraicGeometry.Scheme
