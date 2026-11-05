/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreePresentedScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeOrdinaryPullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImagePullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageColumns
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedFiniteFreeScalarCoordinates

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarModels
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite-free direct-image coefficient coherence

Source: Stacks Project, Tags 0B56 and 0944
(blueprint: lem-sp-finite-free-direct-image-coherence).

All module and derived categories are the existing ones. The auxiliary records bundle
coefficient squares and normalized presentations of the existing scalar functors.
Balancing is the conjugate of the canonical restriction/direct-image comparison, and
its right mate is the specified counit-tensor map. No arbitrary comparison is bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

set_option maxHeartbeats 800000 in
-- The inlined coordinate construction exceeded 200000 heartbeats at the derived square.
private theorem comparison_isIso_app {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    IsIso ((comparison sW sZ a).app M) := by
  classical
  have hcolumns : ∃ (eW : (⨁ fun _ : Fin d ↦
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≅
        (proEtaleRingRestrictScalars a.target).mapDerivedCategory.obj
          ((sW.presentation a.target).derived.obj
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M)))
      (eZ : (⨁ fun _ : Fin d ↦ M) ≅
        (proEtaleRingRestrictScalars a.source).mapDerivedCategory.obj
          ((sZ.presentation a.source).derived.obj M)),
      ∀ i : Fin d,
        biproduct.ι _ i ≫ eW.hom ≫
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
            ((comparison sW sZ a).app M) ≫
          (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm).hom.app
              ((sZ.presentation a.source).derived.obj M) =
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
          (biproduct.ι _ i ≫ eZ.hom) := by
    let θ := basisPowerIso W R.target d ≪≫ hfree.some.symm
    obtain ⟨θZ, hcoord⟩ := finiteFreeDirectImage_coefficientPullback R S a d θ
    obtain ⟨φW, _, _, hεW, hW⟩ :=
      finiteFreeDirectImage_presentedScalarCoordinates W sW a.target d θ
    obtain ⟨φZ, _, _, hεZ, hZ⟩ := finiteFreeDirectImage_presentedScalarCoordinates Z sZ a.source d
      θZ
    have hordinary (M : proEtaleRingModules W R.target) :
      (proEtaleRingModulePullback q R.target R.source R.identification).map (φW.hom.app M) ≫
        (PreservesProduct.iso (proEtaleRingModulePullback q R.target R.source R.identification)
          (fun _ : Fin d ↦ M)).hom =
      (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).app
          ((sW.presentation a.target).ordinary.obj M) ≫
        (proEtaleRingRestrictScalars a.source).map ((ordinaryBalancing sW sZ a).hom.app M) ≫
        φZ.hom.app ((proEtaleRingModulePullback q R.target R.source R.identification).obj M) := by
      let F := proEtaleRingModulePullback q R.target R.source R.identification
      let adj := proEtaleRingModuleAdjunction q R.target R.source R.identification
      apply limit.hom_ext
      rintro ⟨i⟩
      change (F.map (φW.hom.app M) ≫ (PreservesProduct.iso F (fun _ : Fin d ↦ M)).hom) ≫
          Pi.π (fun _ : Fin d ↦ F.obj M) i = _
      rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, ← F.map_comp]
      apply (adj.homEquiv _ _).injective
      simp only [Adjunction.homEquiv_unit]
      erw [← adj.unit.naturality (φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i)]
      apply presentedTensor_hom_ext W sW a.target d θ
      intro V b m
      change ((adj.unit.app M).val.app V)
          ((φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
            (sectionTensor (sW.presentation a.target) M V b m)) =
        (φZ.hom.app (F.obj M) ≫ Pi.π (fun _ : Fin d ↦ F.obj M) i).val.app
          ((proEtaleBaseChange q).op.obj V)
          (((ordinaryBalancing sW sZ a).hom.app M).val.app ((proEtaleBaseChange q).op.obj V)
            (((proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
              a.target a.source R.identification S.identification a.comm).app
                ((sW.presentation a.target).ordinary.obj M)).val.app
                  ((proEtaleBaseChange q).op.obj V)
                    ((adj.unit.app _).val.app V
                      (sectionTensor (sW.presentation a.target) M V b m))))
      erw [hW M V b m i]
      erw [((adj.unit.app M).val.app V).hom.map_smul]
      erw [restrictionPullback_unit R S a ((sW.presentation a.target).ordinary.obj M) V
        (sectionTensor (sW.presentation a.target) M V b m)]
      erw [ordinaryBalancing_pure sW sZ a M V b m]
      erw [hZ (F.obj M) ((proEtaleBaseChange q).op.obj V)
        ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b)
        ((adj.unit.app M).val.app V m) i, hcoord V b i]
      rfl
    let T := (sW.presentation a.target).ordinary
    let T' := (sZ.presentation a.source).ordinary
    let U := proEtaleRingRestrictScalars a.target
    let U' := proEtaleRingRestrictScalars a.source
    let F := proEtaleRingModulePullback q R.target R.source R.identification
    let G := proEtaleRingModulePullback q S.target S.source S.identification
    let E := (sW.presentation a.target).derived
    let E' := (sZ.presentation a.source).derived
    let εh := (sW.presentation a.target).counit
    let εh' := (sZ.presentation a.source).counit
    let (H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ)) :
        IsIso (εh.app H) := hεW H
    let : IsIso εh := NatIso.isIso_of_isIso_app _
    let (H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ)) :
        IsIso (εh'.app H) := hεZ H
    let : IsIso εh' := NatIso.isIso_of_isIso_app _
    let ε : DerivedCategory.Q ⋙ E ⟶
        T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      { app := fun K ↦ εh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
        naturality := by
          intro X Y f
          exact εh.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
    let ε' : DerivedCategory.Q ⋙ E' ⟶
        T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      { app := fun K ↦ εh'.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
        naturality := by
          intro X Y f
          exact εh'.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
    have : IsIso ε := by
      have (K : CochainComplex (proEtaleRingModules W R.target) ℤ) : IsIso (ε.app K) :=
        inferInstanceAs (IsIso (εh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
      exact NatIso.isIso_of_isIso_app _
    have : IsIso ε' := by
      have (K : CochainComplex (proEtaleRingModules Z R.source) ℤ) : IsIso (ε'.app K) :=
        inferInstanceAs (IsIso (εh'.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
      exact NatIso.isIso_of_isIso_app _
    let χ := ordinaryBalancing sW sZ a
    let := proEtaleRingRestrictionPullbackInv_isIso q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm
    let ρ := asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)
    let Φ := SheafOfModules.RingedTensor.coordinateDescent T U d E ε φW
    let Φ' := SheafOfModules.RingedTensor.coordinateDescent T' U' d E' ε' φZ
    let β := SheafOfModules.RingedTensor.scalarComparisonDescent T F G T' E ε E' ε' χ
    let ρD := Functor.mapDerivedCategoryCompIso U F ≪≫
      Functor.mapDerivedCategoryNatIso ρ ≪≫ (Functor.mapDerivedCategoryCompIso G U').symm
    let τ := Functor.whiskerLeft E ρD.hom ≫
      Functor.whiskerRight β.hom U'.mapDerivedCategory
    have hρD : ρD.hom = (proEtaleRingRestrictionDerivedPullback q R.target S.target
        R.source S.source a.target a.source R.identification S.identification a.comm).inv := by
      simp only [ρD, proEtaleRingRestrictionDerivedPullback,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
      rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq]
    have hsquare (M : proEtaleRingModules W R.target) :
        F.map (φW.hom.app M) ≫ (SheafOfModules.RingedTensor.powerComparison F d).hom.app M =
          ρ.hom.app (T.obj M) ≫ U'.map (χ.hom.app M) ≫ φZ.hom.app (F.obj M) := by
      unfold SheafOfModules.RingedTensor.powerComparison
      exact hordinary M
    have hτ (X : DerivedCategory (proEtaleRingModules W R.target)) :
        F.mapDerivedCategory.map (Φ.hom.app X) ≫
          (SheafOfModules.RingedTensor.powerComparison F.mapDerivedCategory d).hom.app X =
        τ.app X ≫ Φ'.hom.app (F.mapDerivedCategory.obj X) := by
      simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.assoc] using
        SheafOfModules.RingedTensor.derivedCoordinateSquare T U d F G T' U' E ε E' ε' χ
        ρ φW φZ hsquare Φ Φ'
        (SheafOfModules.RingedTensor.coordinateDescent_normalized T U d E ε φW)
        (SheafOfModules.RingedTensor.coordinateDescent_normalized T' U' d E' ε' φZ) X
    let eW (X : DerivedCategory (proEtaleRingModules W R.target)) :=
      biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ.app X).symm
    let eZ (X : DerivedCategory (proEtaleRingModules Z R.source)) :=
      biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ'.app X).symm
    have hβ : BalancingComputed sW sZ a β := by
      have hF (K : CochainComplex (proEtaleRingModules W R.target) ℤ) :
          F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
            F.mapDerivedCategoryFactors.hom.app K := by
        rw [F.mapDerivedCategoryFactorsh_hom_app]
        change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app K ≫
          𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
        simp
      have hG (K : CochainComplex (proEtaleRingModules W S.target) ℤ) :
          G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
            G.mapDerivedCategoryFactors.hom.app K := by
        rw [G.mapDerivedCategoryFactorsh_hom_app]
        change G.mapDerivedCategory.map (𝟙 _) ≫ G.mapDerivedCategoryFactors.hom.app K ≫
          𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
        simp
      intro H
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
      rw [hF]
      erw [hG]
      have h := SheafOfModules.RingedTensor.scalarComparisonDescent_normalized T F G T'
        E ε E' ε' χ K
      have hh : DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
            (χ.hom.mapHomotopyCategory (.up ℤ)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) =
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
              (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K) := by
        simp only [Functor.map_comp]
        rfl
      rw [hh]
      exact h
    have heq : β = balancing sW sZ a :=
      finiteFreeDirectImage_balancingComputed sW sZ a β hεZ hβ
    have hnat {X Y : DerivedCategory (proEtaleRingModules Z R.source)} (f : X ⟶ Y)
        (i : Fin d) :
        biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom ≫
            U'.mapDerivedCategory.map (E'.map f) =
          f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫ (eZ Y).hom := by
      simpa only [eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        Functor.comp_map, Category.assoc] using
        coordinateInjection_naturality d (E' ⋙ U'.mapDerivedCategory) Φ' f i
    have hpull (X : DerivedCategory (proEtaleRingModules W R.target)) (i : Fin d) :
        F.mapDerivedCategory.map (biproduct.ι _ i ≫ (eW X).hom) ≫
            (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
              a.target a.source R.identification S.identification a.comm).inv.app (E.obj X) ≫
            U'.mapDerivedCategory.map (β.hom.app X) =
          biproduct.ι _ i ≫ (eZ (F.mapDerivedCategory.obj X)).hom := by
      have h := coordinateInjection_square d F.mapDerivedCategory
        (E ⋙ U.mapDerivedCategory) (E' ⋙ U'.mapDerivedCategory) Φ Φ' τ hτ X i
      simpa only [τ, eW, eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.assoc, hρD] using h
    refine ⟨eW _, eZ M, fun i ↦ ?_⟩
    simpa only [comparison, heq, Category.assoc] using mate_columns
      (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
      (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
      (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm)
      β
      (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm)
      (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).2.2
      (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eW X).hom)
      (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom)
      (fun {X Y} f i ↦ by simpa only [Category.assoc] using hnat f i) hpull M i
  obtain ⟨eW, eZ, hcol⟩ := hcolumns
  let G := proEtaleRingDerivedDirectImage q R.target R.source R.identification
  let U := (proEtaleRingRestrictScalars a.target).mapDerivedCategory
  let δ := proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let f := (comparison sW sZ a).app M
  have heq : eW.hom ≫ U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M) =
      (Functor.mapBiproduct G (fun _ : Fin d ↦ M)).inv ≫ G.map eZ.hom := by
    apply biproduct.hom_ext'
    intro i
    simpa only [Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      ← G.map_comp] using hcol i
  have : IsIso (eW.hom ≫ U.map f ≫
      δ.hom.app ((sZ.presentation a.source).derived.obj M)) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M)) :=
    IsIso.of_isIso_comp_left eW.hom _
  have : IsIso (U.map f) := IsIso.of_isIso_comp_right _
    (δ.hom.app ((sZ.presentation a.source).derived.obj M))
  have : U.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.1
  exact isIso_of_reflects_iso f U

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
