/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AcyclicFlatProperCoefficientModel
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.Paper.ProperOpenCoefficientRefinement
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat
import Sheaf.AlgebraicGeometry.EtaleSumTensorTestComparison
import all Sheaf.Paper.EtaleOpenScalarExchange
import Sheaf.AlgebraicGeometry.EtaleCompactificationBoundedModels
import all Sheaf.Paper.AcyclicFlatProperCoefficientModel
import all Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap

/-! # Sheetwise computation of the compactified etale coefficient arrow

Source: Stacks Project, more-etale.tex, Tag 0GL6; etale-cohomology.tex,
Tags 03S5 and 0F4L; blueprint Charts paragraph of det-sp-reduction-exceptional
(blueprint: lem-sp-etale-sum-coefficient-computation).

The graph map and derived units fix the model identifications. The coefficient
arrow is the actual proper counit mate followed by the normalized open comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Degreewise open extension of the supplied complex.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
abbrev compactifiedEtaleOpenComplex
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} {e : U ⟶ V}
    (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomologicalComplex (.up ℤ)).obj P

/-- Degreewise proper direct image of open extension.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
abbrev compactifiedEtaleDirectComplex
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} {e : U ⟶ V}
    (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((lowerStar (ModuleCat.{u + 1} A) c.g).mapHomologicalComplex (.up ℤ)).obj
    (compactifiedEtaleOpenComplex A c P)

/-- Degreewise extension along the canonical clopen graphs of the sheets.
Source: Stacks 0F4L, 03S5 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumCompactifiedComplexMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
      (.up ℤ)).obj P ⟶ compactifiedEtaleDirectComplex A c P :=
  (NatTrans.mapHomologicalComplex (etaleCompactificationGraphMap A e c) (.up ℤ)).app P

attribute [local irreducible] etaleSumCompactifiedComplexMap

/-- The specified acyclic-model boundary, from the sum complex to compact supports:
localize the graph map, apply the proper derived unit, and insert the exact open
localization factor. No isomorphism or representative is chosen.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumCompactifiedModelBoundary
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Q.obj P) :=
  DerivedCategory.Q.map (etaleSumCompactifiedComplexMap A e c P) ≫
    properAcyclicComparison A c.g (compactifiedEtaleOpenComplex A c P) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.inv.app P)

attribute [local irreducible] etaleSumCompactifiedModelBoundary

/-- The ordinary sum/scalar isomorphism fixed by the sum/evaluation and scalar
adjunctions and the actual restriction/scalar comparison. It extends scalars on
each sheet, rather than permuting sheets or choosing an endpoint isomorphism.
Source: Stacks 03S5, 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumScalarSheafIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance :=
  ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)).ofNatIsoRight
        (upperStarRestrictScalarsIsoSheaf φ e).symm)

/-- The sheetwise scalar chain map; mapping a natural transformation degreewise
makes it commute with the differentials, including the zero and empty-sheet cases.
Source: Stacks 03S5, 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumScalarComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapHomologicalComplex
        (.up ℤ)).obj (coefficientExtendedComplex φ U P) :=
  (NatTrans.mapHomologicalComplex (etaleSumScalarSheafIso φ e).hom (.up ℤ)).app P

attribute [local irreducible] etaleSumScalarComplexMap

/-- A sheet generator, using the sum-adjunction unit and the identification of etale
inverse image with literal restriction. An object S over U is precisely a test object
with a specified lift to U, so this includes every sheet over every etale test object.
Source: Stacks 03S5, 0F4L (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumSheetMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : U.Etale) :
    M.obj.obj (Opposite.op S) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj.obj
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)) :=
  (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M) ≫
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).hom.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app (Opposite.op S)

/-- The local pure tensor x tensor b, via the actual scalar-adjunction unit. The
explicit identity reads its value in the B-module, before restricting coefficients.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleScalarPureTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : T.Etaleᵒᵖ) (x : M.obj.obj S) (b : B) :
    ((ProEtale.etaleSheafExtendScalars φ T).obj M).obj.obj S :=
  b • @id (((ProEtale.etaleSheafExtendScalars φ T).obj M).obj.obj S)
    ((((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M).hom.app S).hom x)

attribute [local irreducible] upperStar lowerStar ProEtale.etaleSheafExtendScalars
  openImmersionLowerShriek Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  upperStarLowerStarAdjunction ProEtale.etaleSheafExtendScalarsAdjunction
  upperStarIsoLocalizationRestriction properAcyclicComparison
  scalarExtensionRepresentative ProEtale.pbcFixedScalarExtension
  Functor.mapHomologicalComplexCompIso NatIso.mapHomologicalComplex
  Functor.leftAdjoint Functor.rightAdjoint scalarMate
  Functor.mapHomotopyCategoryFactors Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCounit Adjunction.ofIsRightAdjoint
  Adjunction.derivedAdjunction derivedUpperStarLowerStarAdjunction
  mateEquiv scalarPullbackIso openScalarExtension
  properOpenCoefficientOpenIso openScalarExtensionZero
  Functor.mapDerivedCategoryFactorsh Sheaf.monoidalCategory
  MorphismProperty.kFlat HomologicalComplex.quasiIso

attribute [local instance 2000] supportedHasSheafify
  cachedPreadditive cachedCoproducts cachedColimits cachedFlatResolution
  cachedInjectiveResolution cachedExactColimits cachedTensor4 cachedTensor12
  cachedTensor23 cachedTensorLeft cachedTensorRight

set_option backward.isDefEq.respectTransparency false in
private theorem sum_scalar_iso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleSumScalarSheafIso φ e = sum_scalar_iso φ e := by
  let a := etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let b := etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance
  let x := ProEtale.etaleSheafExtendScalarsAdjunction φ V
  let v := ProEtale.etaleSheafExtendScalarsAdjunction φ U
  let iA := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance
  let iB := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((a.comp x).homEquiv _ _).injective
  dsimp only [sum_scalar_iso]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp x)
    ((v.comp (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance)).ofNatIsoRight
        (upperStarRestrictScalarsIsoSheaf φ e).symm) M
  change _ ≫ _ = _ at hu
  have hR : upperStarRestrictScalarsIsoSheaf φ e =
      Functor.isoWhiskerLeft (Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ) iA ≪≫
        Functor.isoWhiskerRight iB.symm (Sheaf.restrictScalars.{u + 1} U.smallEtaleTopology φ) :=
    Iso.ext (literal_scalar_pullback φ e)
  have hRi := congrArg Iso.inv hR
  dsimp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv] at hRi
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Iso.symm_hom] at hu
  rw [hRi] at hu
  simp only [etaleLowerShriekUpperStarAdjunction] at hu
  change ((a.ofNatIsoRight iA.symm).comp x).unit.app M ≫ _ =
    (v.comp (b.ofNatIsoRight iB.symm)).unit.app M ≫ _ at hu
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.comp_map, Category.assoc] at hu
  change a.unit.app M ≫ iA.inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) e).map (x.unit.app _) ≫
        (upperStar (ModuleCat.{u + 1} A) e).map
          ((Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ).map
            ((etaleSumScalarSheafIso φ e).hom.app M)) = _ at hu
  have hn := iA.inv.naturality
    (x.unit.app ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
      (Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ).map
        ((etaleSumScalarSheafIso φ e).hom.app M))
  simp only [Functor.map_comp, Category.assoc] at hn
  erw [← hn] at hu
  simp only [Functor.map_comp, Category.assoc] at hu
  let N := (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).obj
    ((ProEtale.etaleSheafExtendScalars φ U).obj M)
  have hc : (Sheaf.restrictScalars.{u + 1} U.smallEtaleTopology φ).map (iB.inv.app N) ≫
      (Sheaf.restrictScalars.{u + 1} U.smallEtaleTopology φ).map (iB.hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (Sheaf.restrictScalars.{u + 1} U.smallEtaleTopology φ).map_id _
  erw [reassoc_of% hc] at hu
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc]
  have hi : Mono (iA.inv.app
      ((Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ).obj N)) :=
    inferInstanceAs (Mono ((iA.app
      ((Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ).obj N)).inv))
  apply (cancel_mono (C := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (iA.inv.app ((Sheaf.restrictScalars.{u + 1} V.smallEtaleTopology φ).obj N))).1
  simpa only [Category.assoc, a, b, v, N, Sheaf.restrictScalars,
    Functor.id_obj, Functor.comp_obj] using hu


private theorem sheet_map_eq
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : U.Etale) (x : M.obj.obj (Opposite.op S)) :
    (etaleSumSheetMap A e M S).hom x = etaleSumSection A e M S x := by
  rw [sum_section_eq_unit]
  have hu : (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).unit.app M =
    (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) := by
    simp only [etaleLowerShriekUpperStarAdjunction, etaleLowerShriekAdjunction,
      etaleLowerShriek,
      Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [etaleSumSheetMap, hu, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem open_scalar_iso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : DerivedCategoryModule A U) :
    (properOpenCoefficientOpenIso φ j M).hom = (openScalarExtension φ j).hom.app M := by
  have hi : (openScalarExtension φ j).inv.app M =
      properOpenCoefficientOpenInverse φ j M := by
    apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).homEquiv _ _).injective
    unfold properOpenCoefficientOpenInverse
    dsimp only [Functor.comp_obj]
    rw [Equiv.apply_symm_apply]
    exact scalarOpen_unit φ j M
  have hi' : ((openScalarExtension φ j).app M).inv =
      (properOpenCoefficientOpenIso φ j M).inv := by
    simpa only [Iso.app_inv, properOpenCoefficientOpenIso, Iso.symm_inv, asIso_hom] using hi
  exact (congrArg Iso.hom (Iso.ext_inv hi')).symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_graph_complex
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
        (etaleSumCompactifiedComplexMap A e c P) ≫
      properCoefficientComplexMap φ c.g (compactifiedEtaleOpenComplex A c P) ≫
      ((lowerStar (ModuleCat.{u + 1} B) c.g).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ c.i)
          (.up ℤ)).hom.app P) =
    etaleSumScalarComplexMap φ e P ≫
      etaleSumCompactifiedComplexMap B e c (coefficientExtendedComplex φ U P) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [etaleSumCompactifiedComplexMap, etaleSumScalarComplexMap,
    properCoefficientComplexMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, sum_scalar_iso_eq]
  erw [Category.comp_id, Category.id_comp]
  exact scalar_graph_compat φ e c (P.X n)

private theorem bounded_etaleKFlat
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (b : ℤ) (hb : ∀ n, b < n → IsZero (P.X n))
    (hf : ∀ n, exactFunctor _ _ (MonoidalCategory.tensorRight (P.X n))) :
    etaleKFlat T A P := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let E := Scheme.etaleSumFlatModuleRealization T A
  have : E.IsEquivalence := Scheme.etaleSumTensorTestRealization_isEquivalence T A
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hb
  have : ((Scheme.etaleSumFlatComplexRealization T A).obj P).IsStrictlyLE b := by
    apply (CochainComplex.isStrictlyLE_iff _ b).2
    intro n hn
    exact E.map_isZero (hb n hn)
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ b
  intro n
  apply (Scheme.etaleConstantModule_flat_iff T A (P.X n)).mp
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (P.X n)).symm (hf n), hf n⟩

private def complexCompositeMap {C D E D' : Type*}
    [Category C] [Category D] [Category E] [Category D']
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive D']
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (η : F ⋙ G ⟶ F' ⋙ G') (P : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (G'.mapHomologicalComplex (.up ℤ)).obj ((F'.mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex η (.up ℤ)).app P

private theorem complexCompositeMap_iso {C D E D' : Type*}
    [Category C] [Category D] [Category E] [Category D']
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive D']
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (η : F ⋙ G ≅ F' ⋙ G') (P : CochainComplex C ℤ) :
    complexCompositeMap F G F' G' η.hom P =
      (Functor.mapHomologicalComplexCompIso η (.up ℤ)).hom.app P := by
  unfold complexCompositeMap Functor.mapHomologicalComplexCompIso NatIso.mapHomologicalComplex
  rfl

private theorem paste_coefficient_squares {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Z₀ Z₁ Z₂ Y₀ Y₁ Y₂ W₀ W₁ : D}
    {p : X₀ ⟶ X₁} {a : X₁ ⟶ X₂} {d : X₂ ⟶ X₃} {q : X₃ ⟶ X₄}
    {j : X₄ ⟶ X₅} {s : X₅ ⟶ X₆} {q₀ : X₂ ⟶ Z₀} {tδ : Z₀ ⟶ X₄}
    {sC : Z₀ ⟶ Z₁} {o : Z₁ ⟶ Z₂} {δ : Z₂ ⟶ X₆}
    {tδ' : X₄ ⟶ Z₀} {δ' : X₆ ⟶ Z₂}
    {sD : X₁ ⟶ Y₀} {π : Y₀ ⟶ Y₁} {α : Y₁ ⟶ Z₁}
    {l : Y₁ ⟶ Y₂} {αB : Y₂ ⟶ Z₂} {s₀ : X₀ ⟶ W₀} {t : W₀ ⟶ Y₀}
    {g : W₀ ⟶ W₁} {gb : W₁ ⟶ Y₂}
    (hn : d ≫ q = q₀ ≫ tδ) (ho : j ≫ s ≫ δ' = tδ' ≫ sC ≫ o)
    (htδ : tδ ≫ tδ' = 𝟙 _) (hδ : δ' ≫ δ = 𝟙 _)
    (hp : a ≫ q₀ ≫ sC = sD ≫ π ≫ α) (ha : l ≫ αB = α ≫ o)
    (hs : p ≫ sD = s₀ ≫ t) (hg : t ≫ π ≫ l = g ≫ gb) :
    p ≫ a ≫ d ≫ q ≫ j ≫ s = s₀ ≫ g ≫ gb ≫ αB ≫ δ := by
  have ho' : tδ ≫ j ≫ s = sC ≫ o ≫ δ := by
    have h := congrArg (fun f ↦ tδ ≫ f ≫ δ) ho
    simpa only [Category.assoc, reassoc_of% htδ, hδ, Category.comp_id,
      Category.id_comp] using h
  rw [reassoc_of% hn, ho', reassoc_of% hp, ← reassoc_of% ha,
    reassoc_of% hs, reassoc_of% hg]

private theorem sum_sheet_tensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : U.Etale) (x : M.obj.obj (Opposite.op S)) (b : B) :
    (((etaleSumScalarSheafIso φ e).hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))).hom
      (etaleScalarPureTensor φ V
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
        ((etaleSumSheetMap A e M S).hom x) b) =
      (etaleSumSheetMap B e ((ProEtale.etaleSheafExtendScalars φ U).obj M) S).hom
        (etaleScalarPureTensor φ U M (Opposite.op S) x b) := by
  rw [sum_scalar_iso_eq]
  dsimp only [etaleScalarPureTensor, id]
  rw [map_smul, map_smul, sheet_map_eq, sheet_map_eq]
  exact congrArg (b • ·) (scalar_unit_sheet φ e M S x)

attribute [local irreducible] etaleSumScalarSheafIso etaleSumSheetMap etaleScalarPureTensor

/-- A bounded flat complex computes the actual compactified etale coefficient arrow
by the sheetwise tensor chain map, under the specified graph and acyclic boundaries.
The last equation on generators says x_s tensor b maps to x_s tensor b in the same
sheet; additivity gives the finite-support formula, even when the sheet set is empty.
No flatness or Tor-dimension assumption is made on B over A.

Source: Stacks 0GL6, 03S5, 0F4L; blueprint Charts paragraph
(blueprint: lem-sp-etale-sum-coefficient-computation).

Proof:
1. Properness makes c.Z Noetherian (lem-weil-pbc-finite-type-over-noetherian).
Apply lem-asd-etale-compact-support-normalization to each P.X n in degree zero,
over A and then to its ordinary B-extension. Higher proper direct images vanish;
the degree-zero comparison is extension along the clopen graphs of the sheets.
2. Open extension preserves flatness (lem-coef-etale-open-tensor). Sum extension
preserves flatness (lem-pur-etale-sum-flat-kflat); transport across the preceding
graph comparison to obtain flatness of the direct-image terms. Both functors
preserve the finite support interval. By lem-pc-bounded-above-flat-kflat-site the
open complex and its direct image are K-flat, as are P and its sum extension.
3. Apply lem-sp-acyclic-flat-proper-coefficient-model to j_!P. Its B-acyclicity
hypothesis follows through the ordinary open tensor isomorphism. The theorem
identifies the named proper B-adjoint counit transpose with the degreewise
ordinary projection morphism under the canonical derived units and scalar models.
Compose with the open tensor comparison, normalized to the identity on U.
4. On an etale test object, direct image evaluates on the fibre product. The
ordinary counit sends z tensor b to z tensor the restriction of b. Taking a sheet
component commutes with this restriction, giving x_s tensor b on the same sheet.
Both sum extension and tensor are locally generated by these generators; balancing
and additivity give equality without a globally split test scheme or flatness of B.
5. The formula commutes with differentials, giving (d x_s tensor b)_s on either
side. Naturality of the canonical model comparisons then gives the displayed
localized equality for the actual proper/open coefficient map. Finite support is
preserved; the empty sheet case is the unique map from zero to zero. This also
covers P=0, the identity coefficient map and the zero coefficient ring. -/
theorem etaleSumCoefficientComputation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsNoetherian U] [IsNoetherian V] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (P.X n))) :
    (∀ n : ℤ, exactFunctor _ _
      (MonoidalCategory.tensorRight ((compactifiedEtaleOpenComplex A c P).X n))) ∧
      (∀ n : ℤ, exactFunctor _ _
        (MonoidalCategory.tensorRight ((compactifiedEtaleDirectComplex A c P).X n))) ∧
      etaleKFlat c.Z A (compactifiedEtaleOpenComplex A c P) ∧
      etaleKFlat V A (compactifiedEtaleDirectComplex A c P) ∧
      (∀ (n : ℤ) (q : ℕ), 0 < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((compactifiedEtaleOpenComplex A c P).X n))))) ∧
      (∀ (n : ℤ) (q : ℕ), 0 < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)).X n))))) ∧
      IsIso (properAcyclicComparison A c.g (compactifiedEtaleOpenComplex A c P)) ∧
      IsIso (properAcyclicComparison B c.g
        (compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P))) ∧
      IsIso (etaleSumCompactifiedComplexMap A e c P) ∧
      IsIso (etaleSumCompactifiedComplexMap B e c (coefficientExtendedComplex φ U P)) ∧
      IsIso (scalarExtensionRepresentative φ U P) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
      ((scalarExtension φ V).map (etaleSumCompactifiedModelBoundary A e c P) ≫
          (properCoefficientMap φ c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map
            (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).hom ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
            (scalarExtensionRepresentative φ U P) =
        scalarExtensionRepresentative φ V
            (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (etaleSumScalarComplexMap φ e P) ≫
          etaleSumCompactifiedModelBoundary B e c (coefficientExtendedComplex φ U P)) ∧
      (∀ (n : ℤ) (S : U.Etale) (x : (P.X n).obj.obj (Opposite.op S)) (b : B),
        (((etaleSumScalarSheafIso φ e).hom.app (P.X n)).hom.app
            (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))).hom
            (etaleScalarPureTensor φ V
              ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj (P.X n))
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
              ((etaleSumSheetMap A e (P.X n) S).hom x) b) =
          (etaleSumSheetMap B e ((ProEtale.etaleSheafExtendScalars φ U).obj (P.X n)) S).hom
            (etaleScalarPureTensor φ U (P.X n) (Opposite.op S) x b)) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    obtain ⟨a, b, hb⟩ := hbounded
    obtain ⟨hZ, νA, hνA, hA⟩ := etaleCompactification_bounded_models A
      (Classical.choice (nonempty_etaleCompactSupportNormalization A)) e c
    have : IsNoetherian c.Z := hZ
    obtain ⟨_, νB, hνB, hB⟩ := etaleCompactification_bounded_models B
      (Classical.choice (nonempty_etaleCompactSupportNormalization B)) e c
    have hPB : ∀ n : ℤ, n < a ∨ b < n →
        IsZero ((coefficientExtendedComplex φ U P).X n) := fun n hn ↦
      Functor.map_isZero (ProEtale.etaleSheafExtendScalars φ U) (hb n hn)
    obtain ⟨hacA, _, _, _, hzA, hfA⟩ := hA P a b hb
    obtain ⟨hacB, _, _, _, hzB, _⟩ := hB (coefficientExtendedComplex φ U P) a b hPB
    obtain ⟨hf, hkP, hkO, hkD, hkS⟩ := hfA hflat
    have hzeroA (n : ℤ) (q : ℕ) (hq : 0 < q) :
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((compactifiedEtaleOpenComplex A c P).X n)))) :=
      (hacA n q hq).of_iso
        ((lowerStar (ModuleCat.{u + 1} A) c.g).homologyRightDerivedFunctorObjSingleFunctorIso
          ((compactifiedEtaleOpenComplex A c P).X n) q)
    have hzeroB (n : ℤ) (q : ℕ) (hq : 0 < q) :
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)).X n)))) :=
      (hacB n q hq).of_iso
        ((lowerStar (ModuleCat.{u + 1} B) c.g).homologyRightDerivedFunctorObjSingleFunctorIso
          ((compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)).X n) q)
    have hmodel : IsAcyclicFlatProperCoefficientModel φ c.g
        (compactifiedEtaleOpenComplex A c P) := by
      refine ⟨⟨a, b, fun n hn ↦ (hzA n hn).1⟩,
        fun n ↦ (hf n).1, fun n ↦ (hf n).2.1, hzeroA, ?_⟩
      intro n q hq
      exact (hzeroB n q hq).of_iso
        ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).mapIso
            ((DerivedCategory.singleFunctor _ 0).mapIso
              ((openScalarExtensionZero φ c.i).app (P.X n)))))
    have hm := acyclicFlatProperCoefficientModel c.g φ
      (compactifiedEtaleOpenComplex A c P) hmodel
    have hisoA := hm.2.2.1
    have hproper := hm.2.2.2.2.2.2.1
    clear hm
    refine ⟨fun n ↦ (hf n).1, fun n ↦ (hf n).2.1, ?_, ?_, hzeroA, hzeroB,
      hisoA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact bounded_etaleKFlat A c.Z _ b (fun n hn ↦ (hzA n (.inr hn)).1)
        (fun n ↦ (hf n).1)
    · exact bounded_etaleKFlat A V _ b (fun n hn ↦ (hzA n (.inr hn)).2.1)
        (fun n ↦ (hf n).2.1)
    · have : CochainComplex.IsStrictlyGE
          (compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)) a :=
        (CochainComplex.isStrictlyGE_iff _ a).2 (fun n hn ↦ (hzB n (.inl hn)).1)
      exact properAcyclicComparison_isIso B c.g _ a hzeroB
    · have := compactification_graph_isIso A e c
      have (n : ℤ) : IsIso ((etaleSumCompactifiedComplexMap A e c P).f n) := by
        unfold etaleSumCompactifiedComplexMap
        change IsIso ((etaleCompactificationGraphMap A e c).app (P.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    · have := compactification_graph_isIso B e c
      have (n : ℤ) : IsIso
          ((etaleSumCompactifiedComplexMap B e c (coefficientExtendedComplex φ U P)).f n) := by
        unfold etaleSumCompactifiedComplexMap
        change IsIso ((etaleCompactificationGraphMap B e c).app
          ((coefficientExtendedComplex φ U P).X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    · exact scalarRepresentative_isIso φ U P hkP
    · exact scalarRepresentative_isIso φ V _ hkS
    · let δA :=
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.inv.app P
      let o := complexCompositeMap
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (ProEtale.etaleSheafExtendScalars φ c.Z)
        (ProEtale.etaleSheafExtendScalars φ U)
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i)
        (openScalarExtensionZero φ c.i).hom P
      have hn := (properCoefficientMap φ c.g).naturality δA
      have ho := (etaleOpenTensorComparisons φ c.i).q_normalized P
        (bounded_etaleKFlat A U P b (fun n hn ↦ hb n (.inr hn)) hflat)
      have hs := (scalarRepresentativeTransformation φ V).naturality
        (etaleSumCompactifiedComplexMap A e c P)
      simp only [scalarRepresentativeTransformation_app, complexLocalization,
        Functor.comp_map] at hs
      have ha := acyclicComparison_naturality B c.g
        (C := coefficientExtendedComplex φ c.Z (compactifiedEtaleOpenComplex A c P))
        (C' := compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)) o
      have ho_eq : o =
          (Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ c.i)
            (.up ℤ)).hom.app P := complexCompositeMap_iso _ _ _ _ _ _
      rw [ho_eq] at ha
      have hg := congrArg DerivedCategory.Q.map (scalar_graph_complex φ e c P)
      simp only [Functor.map_comp] at hg
      dsimp only [derivedExtension] at ho
      dsimp only [properCoefficientTensor] at hproper
      have hRo := congrArg (rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map ho
      simp only [Functor.map_comp] at hRo
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      dsimp only [rightDerivedLowerStar, Functor.comp_obj, Functor.comp_map] at hn hRo hproper ha
      have hd := paste_coefficient_squares hn hRo
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          dsimp only [δA]
          rw [Iso.inv_hom_id_app]
          dsimp only [Functor.comp_obj]
          rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
        (by
          rw [← Functor.map_comp, Iso.hom_inv_id_app]
          dsimp only [Functor.comp_obj]
          rw [CategoryTheory.Functor.map_id])
        hproper ha hs hg
      rw [open_scalar_iso_eq]
      simpa only [etaleSumCompactifiedModelBoundary,
        rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
        Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc,
        δA, coefficientExtendedComplex, compactifiedEtaleOpenComplex] using hd
    · exact fun n S x b ↦ sum_sheet_tensor φ e (P.X n) S x b

end AlgebraicGeometry.Etale
