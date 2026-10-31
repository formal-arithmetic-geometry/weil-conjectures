/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.AcyclicFlatProperCoefficientModel
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleFlat
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTestComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
import WeilConjectures.AlgebraicGeometry.Etale.EtaleCompactificationBoundedModels
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.AcyclicFlatProperCoefficientModel
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleCompactificationSheafScalarMap

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

attribute [local irreducible] etaleSumScalarSheafIso etaleSumSheetMap etaleScalarPureTensor

end AlgebraicGeometry.Etale
