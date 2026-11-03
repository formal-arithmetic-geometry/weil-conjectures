/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoefMonoidalSquareHomTransport
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
public import WeilConjectures.AlgebraicGeometry.EtaleChartComparison.EtaleChartComparisonIsos
public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
public import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
public import WeilConjectures.SixFunctors.NormalizedSiteScalarTensor.NormalizedSiteScalarTensorComposition

/-!
# Finite coefficient scalar/site equation descent

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).

The theorem below uses the actual ordinary derived categories of module sheaves on the
small etale and pro-etale sites.  Its scalar functors are the fixed-coefficient derived
extensions, its site functors are the derived comparison inverse images, and its square
is the published balanced K-flat comparison iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance 2000] isNoetherian_of_finite

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures
open AlgebraicGeometry

namespace WeilConjectures

private theorem siteEquation_transport_tensor_counit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) {P P' Q Q' T T' : C} {EP EP' EQ EQ' ET ET' V V' : D}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T')
    (e : EP ≅ EP') (f : EQ ≅ EQ') (d : ET ≅ ET') (g : V ≅ V')
    (t : P ⊗ Q ⟶ T) (t' : EP ⊗ EQ ⟶ V)
    (εP : L.obj P ⟶ EP) (εQ : L.obj Q ⟶ EQ) (εT : L.obj T ⟶ ET)
    (δ : ET ⟶ V) (δ' : ET' ⟶ V')
    (τ : L.obj (P ⊗ Q) ⟶ L.obj P ⊗ L.obj Q)
    (τ' : L.obj (P' ⊗ Q') ⟶ L.obj P' ⊗ L.obj Q')
    (hn : L.map (a.inv ⊗ₘ b.inv) ≫ τ = τ' ≫ (L.map a.inv ⊗ₘ L.map b.inv))
    (hc : τ ≫ (εP ⊗ₘ εQ) ≫ t' = L.map t ≫ εT ≫ δ)
    (hδ : δ ≫ g.hom = d.hom ≫ δ') :
    L.map ((a.inv ⊗ₘ b.inv) ≫ t ≫ c.hom) ≫
        (L.map c.inv ≫ εT ≫ d.hom) ≫ δ' =
      τ' ≫ ((L.map a.inv ≫ εP ≫ e.hom) ⊗ₘ (L.map b.inv ≫ εQ ≫ f.hom)) ≫
        ((e.inv ⊗ₘ f.inv) ≫ t' ≫ g.hom) := by
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  rw [Category.assoc, ← reassoc_of% hn, reassoc_of% hc, hδ]

private noncomputable abbrev siteEquation_complexMonoidalC :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance

private noncomputable abbrev siteEquation_complexMonoidalD :
    MonoidalCategory (CochainComplex D ℤ) := inferInstance

private noncomputable abbrev siteEquation_homotopyMonoidalC :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance

private noncomputable abbrev siteEquation_homotopyMonoidalD :
    MonoidalCategory (HomotopyCategory D (.up ℤ)) := inferInstance

private noncomputable abbrev siteEquation_derivedMonoidalC : MonoidalCategory (DerivedCategory C) :=
  inferInstance

private noncomputable abbrev siteEquation_derivedMonoidalD : MonoidalCategory (DerivedCategory D) :=
  inferInstance

private lemma siteEquation_comparison_naturality_tensorHom {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫
        (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  simpa only [F.leftDerivedFunctorMonoidal_δ] using
    (OplaxMonoidal.δ_natural F.leftDerivedFunctor f g).symm

private lemma siteEquation_tensorator_Q (P Q : CochainComplex C ℤ) :
    LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app
        (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) := by
  change (_ ⊗ₘ _) ≫ (_ ≫ Qh.map (𝟙 _)) ≫ _ = _
  simp only [Qh.map_id, Category.comp_id]
  rfl

private lemma siteEquation_comparison_cochain (P Q : CochainComplex C ℤ) :
    F.leftDerivedFunctor.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
        F.rightExact_cochainCounit (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
        (DerivedCategory.Q (C := D)).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      (F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
        (F.rightExact_cochainCounit P ⊗ₘ F.rightExact_cochainCounit Q) ≫
        LaxMonoidal.μ (DerivedCategory.Q (C := D))
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
  rw [siteEquation_tensorator_Q, siteEquation_tensorator_Q]
  let p := HomotopyCategory.quotient C (.up ℤ)
  let q := HomotopyCategory.quotient D (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  let e' := DerivedCategory.quotientCompQhIso D
  let δ := ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom
    (p.obj P) (p.obj Q)
  have ht := siteEquation_transport_tensor_counit
    (C := DerivedCategory C) (D := DerivedCategory D) F.leftDerivedFunctor (e.app P) (e.app Q)
    (e.app (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj
      (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    (e'.app (((curriedTensor (CochainComplex D ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (LaxMonoidal.μ (Qh (C := C)) (p.obj P) (p.obj Q))
    (LaxMonoidal.μ (Qh (C := D)) (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
      (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (F.leftDerivedFunctorCounit.app (p.obj P))
    (F.leftDerivedFunctorCounit.app (p.obj Q))
    (F.leftDerivedFunctorCounit.app (p.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    ((Qh (C := D)).map (q.map δ)) ((DerivedCategory.Q (C := D)).map δ)
    ((F.leftDerivedTensorComparison.app (Qh.obj (p.obj P))).app (Qh.obj (p.obj Q)))
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj Q))
    (F.siteEquation_comparison_naturality_tensorHom (e.inv.app P) (e.inv.app Q)) h
    (DerivedCategory.quotientCompQhIso_hom_naturality δ)
  dsimp only [p, q, e, e', δ] at ht
  unfold rightExact_cochainCounit
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Iso.app_hom, Iso.app_inv, MonoidalCategory.curriedTensor_obj_obj] at ht ⊢
  simpa only [Category.assoc] using ht

private theorem representativeAux (adj : E ⊣ U) (ad : L ⊣ U.mapDerivedCategory)
    (P : CochainComplex C ℤ) :
    finiteVerdierScalarRepresentativeAux E U adj ad P =
      (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
  unfold finiteVerdierScalarRepresentativeAux
  rw [← Etale.mapComplex_unit_formula]
  rfl

private theorem normalization_pointwise (adj : E ⊣ U) (ad : L ⊣ U.mapDerivedCategory)
    (P Q : CochainComplex C ℤ) :
    let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    let e := ad.leftAdjointUniq b
    letI := E.leftDerivedFunctorMonoidal
    letI := Functor.Monoidal.transport e.symm
    Functor.OplaxMonoidal.δ L (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (finiteVerdierScalarRepresentativeAux E U adj ad P ⊗ₘ
        finiteVerdierScalarRepresentativeAux E U adj ad Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((E.mapHomologicalComplex (.up ℤ)).obj P)
        ((E.mapHomologicalComplex (.up ℤ)).obj Q) =
    L.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      finiteVerdierScalarRepresentativeAux E U adj ad (P ⊗ Q) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app P).app Q) := by
  dsimp only
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := ad.leftAdjointUniq b
  let : E.leftDerivedFunctor.Monoidal := E.leftDerivedFunctorMonoidal
  let : L.Monoidal := Functor.Monoidal.transport e.symm
  have hr (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P =
        finiteVerdierScalarRepresentativeAux E U adj ad P := by
    rw [representativeAux]
    simpa only [Functor.rightExact_cochainCounit, Iso.app_inv, Iso.app_hom,
      Category.assoc] using Adjunction.leftDerivedCochainCounit E U adj ad P
  have h := E.siteEquation_comparison_cochain P Q
  rw [Functor.Monoidal.transport_δ]
  dsimp only [e, b, Iso.symm_inv, Iso.symm_hom] at hr ⊢
  rw [← hr P, ← hr Q, ← hr (P ⊗ Q)]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app_assoc]
  have hn := (ad.leftAdjointUniq
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory)).hom.naturality
      (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  rw [Functor.leftDerivedFunctorMonoidal_δ, ← h, ← reassoc_of% hn]
  rfl

/-- The ordinary scalar extension is left adjoint to exact restriction.
Source: Stacks 03EK and 06YY; tensor and adjunction constructions in blueprint
thm-coef-finite-hom, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
instance (priority := 100) finiteCoefficientOrdinaryScalarLeft
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : (finiteVerdierOrdinaryExtension J f).IsLeftAdjoint :=
  (finiteVerdierOrdinaryAdjunction J f).isLeftAdjoint

/-- Balanced scalar extension preserves flat module sheaves.
Source: Stacks 03EK and 06YY; tensor and adjunction constructions in blueprint
thm-coef-finite-hom, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
instance (priority := 100) finiteCoefficientOrdinaryScalarFlat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : (finiteVerdierOrdinaryExtension J f).PreservesFlat :=
  ⟨fun hM ↦ CategoryTheory.Sheaf.flat_extendScalars_obj J f hM⟩

/-- Scalar extension preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks 03EK and 06YY; tensor and adjunction constructions in blueprint
thm-coef-finite-hom, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
instance (priority := 100) finiteCoefficientOrdinaryScalarKFlat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (finiteVerdierOrdinaryExtension J f).PreservesKFlatQuasiIso := by
  let E := finiteVerdierOrdinaryExtension J f
  classical
  let U := CategoryTheory.Sheaf.restrictScalars J f
  let B' := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).obj
    (ModuleCat.of B B)
  let X' := (Functor.const Cᵒᵖ).obj B'
  let a := presheafToSheaf J (ModuleCat.{u + 1} A)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
  let F' := sheafToPresheaf J (ModuleCat.{u + 1} A)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)
  have hs : J.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X') :=
    Functor.associator F' (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F' (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F' (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)
          (sheafificationAdjunction J (ModuleCat.{u + 1} B))
          (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
      Functor.isoWhiskerLeft F' (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F' (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} f) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F' (Sheaf.presheafToSheafCompTensorRightIso X').symm ≪≫
      (Functor.associator F' a (MonoidalCategory.tensorRight (a.obj X'))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
        (MonoidalCategory.tensorRight (a.obj X')) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have hc : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf J (ModuleCat.{u + 1} A)) := IsGrothendieckAbelian.hasColimits _
  have hc0 : HasColimitsOfSize.{0, 0}
      (Sheaf J (ModuleCat.{u + 1} A)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have hcc : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X')
  have hEU := ht.of_iso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
  have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
    hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
      (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)

/-- The canonical balanced tensor structure of ordinary coefficient extension.
Source: Stacks 03EK, 06YY; blueprint thm-coef-finite-hom, final paragraph.
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
@[instance_reducible]
noncomputable def finiteCoefficientOrdinaryScalarMonoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : (finiteVerdierOrdinaryExtension J f).Monoidal := by
  let E := finiteVerdierOrdinaryExtension J f
  let : E.OplaxMonoidal := CategoryTheory.composeAndSheafifyOplaxMonoidal J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  let (M N : _) : IsIso (Functor.OplaxMonoidal.δ E M N) :=
    CategoryTheory.isIso_δ_composeAndSheafify J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f) M N
  let : IsIso (Functor.OplaxMonoidal.η E) :=
    CategoryTheory.isIso_η_composeAndSheafify J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  exact .ofOplaxMonoidal E

/-- The canonical identification of the chosen scalar adjoint with ordinary derived extension.
Source: Stacks 03EK, 06YY; blueprint thm-coef-finite-hom, final paragraph.
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
noncomputable def finiteCoefficientScalarDerivedIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : Sheaf.fixedCoefficientDerivedScalarExtension J f ≅
      (finiteVerdierOrdinaryExtension J f).leftDerivedFunctor :=
  (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J f)).leftAdjointUniq
    ((finiteVerdierOrdinaryAdjunction J f).derivedAdjunction.ofNatIsoRight
      (CategoryTheory.Sheaf.restrictScalars J f).rightDerivedFunctorIsoMapDerivedCategory)

/-- A canonical K-flat tensorator for fixed-coefficient derived extension.

The ordinary sheafified scalar extension is strong monoidal by the balanced module tensor.
Its left derived monoidal structure is transported along the unique adjunction isomorphism to
`fixedCoefficientDerivedScalarExtension`; this pins the tensorator on K-flat representatives
rather than choosing an arbitrary monoidal structure.
Source: Stacks Tags 03EK, 06YY and 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
@[instance_reducible]
noncomputable def finiteCoefficientScalarMonoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension J f).Monoidal := by
  let E := finiteVerdierOrdinaryExtension J f
  let : E.Monoidal := finiteCoefficientOrdinaryScalarMonoidal J f
  letI : E.PreservesKFlatQuasiIso := finiteCoefficientOrdinaryScalarKFlat J f
  let : E.leftDerivedFunctor.Monoidal := E.leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport (finiteCoefficientScalarDerivedIso J f).symm

private def canonicalUncurriedTensorIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] :
    Functor.uncurry.obj (curriedTensor C) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) :=
  NatIso.ofComponents (fun Z ↦ (Functor.Monoidal.μIso F Z.1 Z.2).symm) (by
    intro X Y f
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      Iso.symm_hom, Functor.Monoidal.μIso_inv, MonoidalCategory.tensorHom_def,
      Category.assoc] using
      (Functor.OplaxMonoidal.δ_natural F f.1 f.2).symm)

private theorem canonicalUncurriedTensorIso_hom_app
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (P Q : C) :
    (canonicalUncurriedTensorIso F).hom.app (P, Q) = Functor.OplaxMonoidal.δ F P Q := rfl

private theorem tensor_square_from_uncurried
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (F : C ⥤ D) (G : E ⥤ H) (U : C ⥤ E) (V : D ⥤ H)
    [F.Monoidal] [G.Monoidal] (a : F ⋙ V ≅ U ⋙ G)
    (tU : (Functor.postcompose₂.obj U).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj U).obj U).obj (curriedTensor E))
    (tV : (Functor.postcompose₂.obj V).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ H).obj V).obj V).obj (curriedTensor H))
    (K M : C)
    (h : a.hom.app (K ⊗ M) ≫ G.map ((tU.app K).app M) ≫
        (canonicalUncurriedTensorIso G).hom.app (U.obj K, U.obj M) =
      V.map ((canonicalUncurriedTensorIso F).hom.app (K, M)) ≫
        (tV.app (F.obj K)).app (F.obj M) ≫ (a.hom.app K ⊗ₘ a.hom.app M)) :
    a.hom.app (K ⊗ M) ≫ G.map ((tU.app K).app M) ≫
        Functor.OplaxMonoidal.δ G (U.obj K) (U.obj M) =
      (V.map (Functor.OplaxMonoidal.δ F K M) ≫
        (tV.app (F.obj K)).app (F.obj M)) ≫ (a.hom.app K ⊗ₘ a.hom.app M) := by
  simpa only [canonicalUncurriedTensorIso_hom_app, Category.assoc] using h

private theorem monoidal_of_expanded_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (F : C ⥤ D) (G : E ⥤ H) (U : C ⥤ E) (V : D ⥤ H)
    [F.Monoidal] [G.Monoidal] [U.Monoidal] [V.Monoidal] (a : F ⋙ V ≅ U ⋙ G)
    (h : ∀ K M : C,
      a.hom.app (K ⊗ M) ≫ G.map (Functor.OplaxMonoidal.δ U K M) ≫
          Functor.OplaxMonoidal.δ G (U.obj K) (U.obj M) =
        (V.map (Functor.OplaxMonoidal.δ F K M) ≫
          Functor.OplaxMonoidal.δ V (F.obj K) (F.obj M)) ≫
          (a.hom.app K ⊗ₘ a.hom.app M)) : NatTrans.IsMonoidal a.hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro K M
  simpa only [Functor.OplaxMonoidal.comp_δ] using h K M

/-- The equation package for the displayed monoidal square.  The four tensorators and the
monoidal comparison proof are explicit arguments, so the package cannot replace the canonical
maps by existentially chosen structures.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
def FiniteCoefficientSiteEquationLaws
    {EA : Type u} [Category.{v} EA] [MonoidalCategory EA] [MonoidalClosed EA]
    {EB : Type u₁} [Category.{v₁} EB] [MonoidalCategory EB] [MonoidalClosed EB]
    {PA : Type u₂} [Category.{v₂} PA] [MonoidalCategory PA] [MonoidalClosed PA]
    {PB : Type u₃} [Category.{v₃} PB] [MonoidalCategory PB] [MonoidalClosed PB]
    [BraidedCategory EA] [BraidedCategory EB] [BraidedCategory PA] [BraidedCategory PB]
    (F : EA ⥤ EB) (G : PA ⥤ PB) (UA : EA ⥤ PA) (UB : EB ⥤ PB)
    (h : F ⋙ UB ≅ UA ⋙ G)
    (mF : F.Monoidal) (mG : G.Monoidal) (mUA : UA.Monoidal) (mUB : UB.Monoidal)
    (hm : NatTrans.IsMonoidal h.hom) (successive : Prop) : Prop :=
  letI : F.Monoidal := mF
  letI : G.Monoidal := mG
  letI : UA.Monoidal := mUA
  letI : UB.Monoidal := mUB
  letI : NatTrans.IsMonoidal h.hom := hm
  InternalHomComparisonLaws F ∧
    InternalHomComparisonLaws G ∧
    InternalHomComparisonLaws UA ∧
    InternalHomComparisonLaws UB ∧
    (∀ (K M : EA),
      F.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ F K M ≫
          (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K) ∧
    (∀ (K M : PA),
      G.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ G K M ≫
          (β_ (G.obj K) (G.obj M)).hom ≫ Functor.LaxMonoidal.μ G M K) ∧
    (∀ (K M : EA),
      UA.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ UA K M ≫
          (β_ (UA.obj K) (UA.obj M)).hom ≫ Functor.LaxMonoidal.μ UA M K) ∧
    (∀ (K M : EB),
      UB.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ UB K M ≫
          (β_ (UB.obj K) (UB.obj M)).hom ≫ Functor.LaxMonoidal.μ UB M K) ∧
    (∀ (S T : EA),
      Functor.LaxMonoidal.μ UB (F.obj S) (F.obj T) ≫
          UB.map (Functor.LaxMonoidal.μ F S T) ≫
          UB.map (F.map (β_ S T).hom) ≫
          h.hom.app (T ⊗ S) =
        (h.hom.app S ⊗ₘ h.hom.app T) ≫
          Functor.LaxMonoidal.μ G (UA.obj S) (UA.obj T) ≫
          G.map (Functor.LaxMonoidal.μ UA S T) ≫
          G.map (UA.map (β_ S T).hom)) ∧
    (∀ (K M : EA),
      h.hom.app (K ⟶[EA] M) ≫
          G.map (internalHomComparison UA K M) ≫
          internalHomComparison G (UA.obj K) (UA.obj M) =
        UB.map (internalHomComparison F K M) ≫
          internalHomComparison UB (F.obj K) (F.obj M) ≫
          internalHomTransport h K M) ∧
    NatTrans.IsMonoidal h.hom ∧ successive

/-- The ordinary derived category on the small etale site with constant coefficients.
Source: blueprint `def-weil-sheaf-of-modules-category` and
`def-weil-abstract-derived-category` (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
abbrev finiteEtaleDerivedCategory (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- The ordinary derived category on the small pro-etale site with constant coefficients.
Source: blueprint `def-weil-sheaf-of-modules-category` and
`def-weil-abstract-derived-category` (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
abbrev finiteProEtaleDerivedCategory (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))

private noncomputable instance finiteEtaleDerivedBraided
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    BraidedCategory (finiteEtaleDerivedCategory X R) :=
  DerivedCategory.braidedCategory' _

private noncomputable instance finiteProEtaleDerivedBraided
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    BraidedCategory (finiteProEtaleDerivedCategory X R) :=
  DerivedCategory.braidedCategory' _

/-- Fixed-coefficient derived extension on the small etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteEtaleCoefficientExtension
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : finiteEtaleDerivedCategory X A ⥤ finiteEtaleDerivedCategory X B :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology f

/-- Fixed-coefficient derived extension on the small pro-etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteProEtaleCoefficientExtension
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : finiteProEtaleDerivedCategory X A ⥤ finiteProEtaleDerivedCategory X B :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology X) f

/-- The sheaf-level identity restriction iso used to normalize scalar extension at `RingHom.id`.
Source: the identity restriction-of-scalars equivalence for sheaves of modules, used for the
identity-ring-map clause of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
noncomputable def finiteCoefficientRestrictionIdentityIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.restrictScalars J (RingHom.id A) ≅
      𝟭 (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A)) := by
  refine NatIso.ofComponents (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso ?_) ?_
  · exact Functor.isoWhiskerLeft F.obj
      (ModuleCat.restrictScalarsId.{u + 1, u + 1} A)
  · intro F G φ
    apply (fullyFaithfulSheafToPresheaf J _).map_injective
    ext U y
    exact congrArg (fun q ↦ q y)
      ((ModuleCat.restrictScalarsId.{u + 1, u + 1} A).hom.naturality (φ.hom.app U))

/-- Derived version of `finiteCoefficientRestrictionIdentityIso`, normalized to the identity
functor by `mapDerivedCategoryIdIso`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
noncomputable def finiteCoefficientDerivedRestrictionIdentityIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.derivedRestrictScalars J (RingHom.id A) ≅
      𝟭 (DerivedCategory (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A))) := by
  simpa only [CategoryTheory.Sheaf.derivedRestrictScalars] using
    Functor.mapDerivedCategoryNatIso (finiteCoefficientRestrictionIdentityIso J) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical derived scalar-extension unitor at an identity ring map.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
noncomputable def finiteCoefficientIdentityUnitor
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension J (RingHom.id A) ≅
      𝟭 (DerivedCategory (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A))) :=
  ((AlgebraicGeometry.CoefficientScalarRepresentatives.adjunction J (RingHom.id A)).ofNatIsoRight
    (finiteCoefficientDerivedRestrictionIdentityIso J)).leftAdjointUniq Adjunction.id

/-- Derived inverse image of the etale-to-pro-etale comparison morphism.
Source: Stacks Project, Tags 03D2 and 07A4 (blueprint: def-weil-pbc-site-comparison-morphism).
-/
noncomputable def finiteSiteComparisonPullback
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    finiteEtaleDerivedCategory X R ⥤ finiteProEtaleDerivedCategory X R :=
  (AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} R) X).mapDerivedCategory

/-- The balanced scalar/site comparison on derived categories.
Source: Stacks Project, Tag 07A4 (blueprint: def-weil-pbc-site-comparison-morphism and
`lem-sfb-scalar-inverse-image-tower-diagram`).  It is the inverse of the published
`comparisonIso` because that declaration is oriented from pullback-after-scalar to
scalar-after-pullback.
-/
noncomputable def finiteCoefficientSiteComparison
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) :
    finiteEtaleCoefficientExtension X f ⋙ finiteSiteComparisonPullback X B ≅
      finiteSiteComparisonPullback X A ⋙ finiteProEtaleCoefficientExtension X f :=
  (AlgebraicGeometry.CoefficientScalarRepresentatives.comparisonIso X f).symm

private theorem comparison_monoidal
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (f : A →+* B) :
    let : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
    let : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
    let : (finiteSiteComparisonPullback X A).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
    let : (finiteSiteComparisonPullback X B).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
    NatTrans.IsMonoidal (finiteCoefficientSiteComparison X f).hom := by
  dsimp only
  let : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
  let : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
  let : (finiteSiteComparisonPullback X A).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  let : (finiteSiteComparisonPullback X B).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
  exact monoidal_of_expanded_square
    (finiteEtaleCoefficientExtension X f) (finiteProEtaleCoefficientExtension X f)
    (finiteSiteComparisonPullback X A) (finiteSiteComparisonPullback X B)
    (finiteCoefficientSiteComparison X f) (comparison_delta X f)

private theorem comparison_delta
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (f : A →+* B) :
    let : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
    let : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
    let : (finiteSiteComparisonPullback X A).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
    let : (finiteSiteComparisonPullback X B).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
    ∀ K M : finiteEtaleDerivedCategory X A,
      (finiteCoefficientSiteComparison X f).hom.app (K ⊗ M) ≫
          (finiteProEtaleCoefficientExtension X f).map
            (Functor.OplaxMonoidal.δ (finiteSiteComparisonPullback X A) K M) ≫
          Functor.OplaxMonoidal.δ (finiteProEtaleCoefficientExtension X f)
            ((finiteSiteComparisonPullback X A).obj K)
            ((finiteSiteComparisonPullback X A).obj M) =
        ((finiteSiteComparisonPullback X B).map
            (Functor.OplaxMonoidal.δ (finiteEtaleCoefficientExtension X f) K M) ≫
          Functor.OplaxMonoidal.δ (finiteSiteComparisonPullback X B)
            ((finiteEtaleCoefficientExtension X f).obj K)
            ((finiteEtaleCoefficientExtension X f).obj M)) ≫
          ((finiteCoefficientSiteComparison X f).hom.app K ⊗ₘ
            (finiteCoefficientSiteComparison X f).hom.app M) := by
  dsimp only
  let : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
  let : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
  let : (finiteSiteComparisonPullback X A).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  let : (finiteSiteComparisonPullback X B).Monoidal :=
      ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
  intro K M
  dsimp only [finiteSiteComparisonPullback]
  rw [generic_site_delta (ModuleCat.{u + 1} A) X,
    generic_site_delta (ModuleCat.{u + 1} B) X]
  have h := tensor_square_from_uncurried
    (finiteEtaleCoefficientExtension X f) (finiteProEtaleCoefficientExtension X f)
    (finiteSiteComparisonPullback X A) (finiteSiteComparisonPullback X B)
    (finiteCoefficientSiteComparison X f)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryTensorComparison
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategoryTensorComparison
    K M
    (normalized_square f X
      (canonicalUncurriedTensorIso (finiteEtaleCoefficientExtension X f))
      (canonicalUncurriedTensorIso (finiteProEtaleCoefficientExtension X f))
      (WeilConjectures.scalarNormalization X.smallEtaleTopology f)
      (WeilConjectures.scalarNormalization (Scheme.ProEt.topology X) f) K M)
  dsimp only [finiteSiteComparisonPullback] at h
  -- Compare the cached instance certificates by explicit, kernel-checked congruence.
  -- Keep the derived functors folded throughout this final presentation conversion.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let hp ← Lean.Meta.getLocalDeclFromUserName `h
      let reduceBy (n : Lean.Name) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let lemmaExpr ← Lean.Meta.mkConstWithFreshMVarLevels n
        let (_, _, body) ← Lean.Meta.forallMetaTelescopeReducing
          (← Lean.Meta.inferType lemmaExpr)
        unless body.isAppOfArity ``Eq 3 do throwError "Expected a reduction equation"
        let args := body.getAppArgs
        unless ← Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq args[1]! e) do
          throwError "Reduction equation does not match the outer expression"
        let result ← Lean.instantiateMVars args[2]!
        if result.hasMVar then throwError "Unresolved reduction equation"
        return result
      let normalize (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let mut e ← Lean.instantiateMVars e
        for _ in [:16] do
          e := e.consumeMData.headBeta
          let name := e.getAppFn.constName?
          if name == some ``inferInstance ||
              name == some ``WeilConjectures.finiteSiteComparisonPullback ||
              name == some ``WeilConjectures.finiteEtaleDerivedCategory ||
              name == some ``WeilConjectures.finiteProEtaleDerivedCategory ||
              name == some ``EtaleChartComparison.Et ||
              name == some ``EtaleChartComparison.Pro ||
              name == some ``EtaleChartComparison.etAbelian ||
              name == some ``EtaleChartComparison.proAbelian ||
              name == some ``EtaleChartComparison.etGroth ||
              name == some ``EtaleChartComparison.proGroth ||
              name == some ``EtaleChartComparison.etMonoidalPreadditive ||
              name == some ``EtaleChartComparison.proMonoidalPreadditive ||
              name == some ``EtaleChartComparison.etSymmetricCategory ||
              name == some ``EtaleChartComparison.proSymmetricCategory ||
              name == some ``EtaleChartComparison.etMonoidalClosed ||
              name == some ``EtaleChartComparison.proMonoidalClosed ||
              name == some ``EtaleChartComparison.etHasFunctorialFlatResolution ||
              name == some ``EtaleChartComparison.proHasFunctorialFlatResolution ||
              name == some ``AlgebraicGeometry.Etale.sheafMonoidalCategory ||
              name == some ``AlgebraicGeometry.Etale.sheafBraidedCategory ||
              name == some ``AlgebraicGeometry.ProEtale.sheafMonoidalCategory ||
              name == some ``AlgebraicGeometry.ProEtale.sheafBraidedCategory ||
              name == some ``AlgebraicGeometry.ProEtale.sheafSymmetricCategory ||
              name == some ``GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall ||
              name == some ``GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall then
            if let some e' ← Lean.Meta.unfoldDefinition? e then
              e ← Lean.instantiateMVars e'
              continue
          if name == some ``Functor.comp then
            let args := e.getAppArgs
            let idx := args.size - 2
            let fnName := args[idx]!.getAppFn.constName?
            if fnName == some ``Functor.comp then
              e ← reduceBy ``Functor.assoc e
              continue
          if name == some ``NatTrans.app then
            let args := e.getAppArgs
            let natName := args[args.size - 2]!.getAppFn.constName?
            let rewriteName : Option Lean.Name :=
              if natName == some ``Functor.whiskerLeft then some ``Functor.whiskerLeft_app
              else if natName == some ``Functor.whiskerRight then some ``Functor.whiskerRight_app
              else if natName == some ``CategoryStruct.comp then some ``NatTrans.comp_app
              else none
            if let some rewriteName := rewriteName then
              e ← reduceBy rewriteName e
              continue
          if name == some ``SymmetricCategory.toBraidedCategory then
            let e' ← Lean.Meta.withTransparency .default (Lean.Meta.whnf e)
            if e' != e then
              e := e'
              continue
          let args := e.getAppArgs
          if name == some ``Functor.obj || name == some ``Functor.map then
            let offset := if name == some ``Functor.obj then 2 else 4
            if args.size < offset then break
            let idx := args.size - offset
            let fnName := args[idx]!.getAppFn.constName?
            if fnName == some ``Functor.comp || fnName == some ``Functor.id then
              let isId := fnName == some ``Functor.id
              let rewriteName : Lean.Name := if name == some ``Functor.obj then
                (if isId then ``Functor.id_obj else ``Functor.comp_obj)
                else (if isId then ``Functor.id_map else ``Functor.comp_map)
              try
                e ← reduceBy rewriteName e
                continue
              catch _ => pure ()
          break
        return e
      let source ← normalize hp.type
      let target ← normalize (← goal.getType)
      let mut pending := [(source, target, false)]
      let mut proofs : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr := {}
      let mut congruences : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem := {}
      for _ in [:100000] do
        if pending.isEmpty then break
        let (a, b, ready) := pending.head!
        pending := pending.tail!
        let a ← normalize a
        let b ← normalize b
        let key := (a, b)
        if proofs.contains key then continue
        if a == b then
          proofs := proofs.insert key (← Lean.Meta.mkHEqRefl a)
        else if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
          proofs := proofs.insert key (← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b])
        else
          let f := a.getAppFn
          let xs := a.getAppArgs
          let ys := b.getAppArgs
          unless f == b.getAppFn && xs.size == ys.size && !xs.isEmpty do
            if ← Lean.Meta.withTransparency .default (Lean.Meta.isDefEq a b) then
              proofs := proofs.insert key (← Lean.Meta.mkHEqRefl a)
              continue
            throwError "Unsupported scalar congruence presentation: {f} versus {b.getAppFn}"
          if !ready then
            pending := (a, b, true) :: pending
            for x in xs, y in ys do
              pending := (x, y, false) :: pending
          else
            let congr ← match congruences[(f, xs.size)]? with
              | some congr => pure congr
              | none => Lean.Meta.mkHCongrWithArity f xs.size
            congruences := congruences.insert (f, xs.size) congr
            let mut proof := congr.proof
            for i in [:xs.size] do
              let child := (← normalize xs[i]!, ← normalize ys[i]!)
              let some h := proofs[child]? | throwError "Missing scalar congruence proof"
              let h ← if congr.argKinds[i]! == .eq then Lean.Meta.mkEqOfHEq h else pure h
              proof := Lean.mkAppN proof #[xs[i]!, ys[i]!, h]
            proofs := proofs.insert key proof
      let key := (source, target)
      let some proof := proofs[key]? | throwError "Scalar congruence traversal unfinished"
      let eq ← Lean.Meta.mkEqOfHEq proof
      let proof ← Lean.Meta.mkAppM ``Eq.mp #[eq, hp.toExpr]
      if proof.hasSorry || proof.hasMVar then throwError "Unfinished scalar congruence proof"
      goal.assign proof

private theorem normalized_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (X : Scheme.{u})
    (δY : Functor.uncurry.obj (curriedTensor (finiteEtaleDerivedCategory X A)) ⋙
        finiteEtaleCoefficientExtension X f ≅
      (finiteEtaleCoefficientExtension X f).prod (finiteEtaleCoefficientExtension X f) ⋙
        Functor.uncurry.obj (curriedTensor (finiteEtaleDerivedCategory X B)))
    (δX : Functor.uncurry.obj (curriedTensor (finiteProEtaleDerivedCategory X A)) ⋙
        finiteProEtaleCoefficientExtension X f ≅
      (finiteProEtaleCoefficientExtension X f).prod
        (finiteProEtaleCoefficientExtension X f) ⋙
        Functor.uncurry.obj (curriedTensor (finiteProEtaleDerivedCategory X B)))
    (hY : Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension.{u} X.smallEtaleTopology f)
      (finiteEtaleCoefficientExtension X f)
      (finiteVerdierScalarRepresentative.{u} X.smallEtaleTopology f) δY)
    (hX : Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension.{u} (Scheme.ProEt.topology X) f)
      (finiteProEtaleCoefficientExtension X f)
      (finiteVerdierScalarRepresentative.{u} (Scheme.ProEt.topology X) f) δX)
    (K M : finiteEtaleDerivedCategory X A) :
    (finiteCoefficientSiteComparison X f).hom.app
        (K ⊗ M) ≫
      (finiteProEtaleCoefficientExtension X f).map
        (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} A) X).mapDerivedCategoryTensorComparison.app K).app
            M) ≫
      δX.hom.app ((finiteSiteComparisonPullback X A).obj K,
        (finiteSiteComparisonPullback X A).obj M) =
    (finiteSiteComparisonPullback X B).map
        (δY.hom.app (K, M)) ≫
      (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} B) X).mapDerivedCategoryTensorComparison.app
          ((finiteEtaleCoefficientExtension X f).obj K)).app
          ((finiteEtaleCoefficientExtension X f).obj M)) ≫
      ((finiteCoefficientSiteComparison X f).hom.app K ⊗ₘ
        (finiteCoefficientSiteComparison X f).hom.app M) := by
  let F := finiteEtaleCoefficientExtension X f
  let G := finiteProEtaleCoefficientExtension X f
  let U := finiteSiteComparisonPullback X A
  let V := finiteSiteComparisonPullback X B
  let TY := Functor.uncurry.obj (curriedTensor (finiteEtaleDerivedCategory X A))
  let TX := Functor.uncurry.obj (curriedTensor (finiteProEtaleDerivedCategory X B))
  let tU := Etale.uncurryTensorComparison U
    (curriedTensor (finiteEtaleDerivedCategory X A))
    (curriedTensor (finiteProEtaleDerivedCategory X A))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryTensorComparison
  let tV := Etale.uncurryTensorComparison V
    (curriedTensor (finiteEtaleDerivedCategory X B))
    (curriedTensor (finiteProEtaleDerivedCategory X B))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategoryTensorComparison
  let a := finiteCoefficientSiteComparison X f
  let α : TY ⋙ F ⋙ V ⟶ U.prod U ⋙ G.prod G ⋙ TX :=
    Functor.whiskerLeft TY a.hom ≫ Functor.whiskerRight tU G ≫
      Functor.whiskerLeft (U.prod U) δX.hom
  let β : TY ⋙ F ⋙ V ⟶ U.prod U ⋙ G.prod G ⋙ TX :=
    Functor.whiskerRight δY.hom V ≫ Functor.whiskerLeft (F.prod F) tV ≫
      Functor.whiskerRight (NatTrans.prod a.hom a.hom) TX
  have hab : α = β := by
    apply Etale.natTrans_ext_flat
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) α β
    intro P R hP hR _ _
    dsimp only [α, β, TY, TX, U, V, F, G, tU, tV, a,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod,
      Etale.uncurryTensorComparison]
    simpa only [Etale.uncurryCurriedTensor_map, curriedTensor_obj_obj,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] using
      normalized_kflat f X δY δX hY hX P R hP hR
  have h := congrArg (fun t ↦ t.app (K, M)) hab
  dsimp only [α, β, TY, TX, U, V, F, G, tU, tV, a,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod,
      Etale.uncurryTensorComparison] at h
  simpa only [Etale.uncurryCurriedTensor_map, curriedTensor_obj_obj,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] using h

private theorem normalized_kflat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (X : Scheme.{u})
    (δY : Functor.uncurry.obj (curriedTensor (finiteEtaleDerivedCategory X A)) ⋙
        finiteEtaleCoefficientExtension X f ≅
      (finiteEtaleCoefficientExtension X f).prod (finiteEtaleCoefficientExtension X f) ⋙
        Functor.uncurry.obj (curriedTensor (finiteEtaleDerivedCategory X B)))
    (δX : Functor.uncurry.obj (curriedTensor (finiteProEtaleDerivedCategory X A)) ⋙
        finiteProEtaleCoefficientExtension X f ≅
      (finiteProEtaleCoefficientExtension X f).prod
        (finiteProEtaleCoefficientExtension X f) ⋙
        Functor.uncurry.obj (curriedTensor (finiteProEtaleDerivedCategory X B)))
    (hY : Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension.{u} X.smallEtaleTopology f)
      (finiteEtaleCoefficientExtension X f)
      (finiteVerdierScalarRepresentative.{u} X.smallEtaleTopology f) δY)
    (hX : Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension.{u} (Scheme.ProEt.topology X) f)
      (finiteProEtaleCoefficientExtension X f)
      (finiteVerdierScalarRepresentative.{u} (Scheme.ProEt.topology X) f) δX)
    (P R : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1, u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (finiteCoefficientSiteComparison X f).hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj R) ≫
      (finiteProEtaleCoefficientExtension X f).map
        (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} A) X).mapDerivedCategoryTensorComparison.app
          (DerivedCategory.Q.obj P)).app
            (DerivedCategory.Q.obj R)) ≫
      δX.hom.app ((finiteSiteComparisonPullback X A).obj (DerivedCategory.Q.obj P),
        (finiteSiteComparisonPullback X A).obj (DerivedCategory.Q.obj R)) =
    (finiteSiteComparisonPullback X B).map
        (δY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj R)) ≫
      (((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} B) X).mapDerivedCategoryTensorComparison.app
          ((finiteEtaleCoefficientExtension X f).obj (DerivedCategory.Q.obj P))).app
          ((finiteEtaleCoefficientExtension X f).obj (DerivedCategory.Q.obj R))) ≫
      ((finiteCoefficientSiteComparison X f).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (finiteCoefficientSiteComparison X f).hom.app (DerivedCategory.Q.obj R)) := by
  let EY := finiteVerdierOrdinaryExtension.{u} X.smallEtaleTopology f
  let EX := finiteVerdierOrdinaryExtension.{u} (Scheme.ProEt.topology X) f
  let FA := ProEtale.comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1, u + 1} A) X
  let FB := ProEtale.comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1, u + 1} B) X
  let : FA.Monoidal := ProEtale.monoidal_comparisonUpperStar.{u + 2, u}
    (ModuleCat.{u + 1, u + 1} A) X
  let : FB.Monoidal := ProEtale.monoidal_comparisonUpperStar.{u + 2, u}
    (ModuleCat.{u + 1, u + 1} B) X
  apply _root_.normalized_cochain_square EY FB FA EX
    (finiteEtaleCoefficientExtension X f) FB.mapDerivedCategory FA.mapDerivedCategory
    (finiteProEtaleCoefficientExtension X f)
    (NormalizedSiteScalarTensor.representative X.smallEtaleTopology f)
    FB.mapDerivedCategoryFactors.hom FA.mapDerivedCategoryFactors.hom
    (NormalizedSiteScalarTensor.representative (Scheme.ProEt.topology X) f)
    (finiteVerdierScalarRepresentative.{u} X.smallEtaleTopology f)
    (fun K ↦ FB.mapDerivedCategoryFactors.hom.app K)
    (fun K ↦ FA.mapDerivedCategoryFactors.hom.app K)
    (finiteVerdierScalarRepresentative.{u} (Scheme.ProEt.topology X) f)
    (NormalizedSiteScalarTensor.representative_app X.smallEtaleTopology f)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (NormalizedSiteScalarTensor.representative_app (Scheme.ProEt.topology X) f)
    δY FB.mapDerivedCategoryTensorComparison FA.mapDerivedCategoryTensorComparison δX hY
    (generic_site_tensor_normalization (ModuleCat.{u + 1, u + 1} B) X)
    (generic_site_tensor_normalization (ModuleCat.{u + 1, u + 1} A) X) hX
    (finiteCoefficientSiteComparison X f) (EtaleChartComparison.scalarSheafIso.{u} f X)
    (Functor.mapHomologicalComplexCompIso (EtaleChartComparison.scalarSheafIso.{u} f X)
      (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (FA ⋙ EX)) (.up ℤ)).symm)
    rfl (ordinary_square f X)
    (by
      intro K _
      simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        Iso.refl_inv, NatTrans.mapHomologicalComplex_id]
      exact OrdinaryScalarSite.delta_equation f X K)
    (NormalizedSiteScalarTensor.representative_iso X.smallEtaleTopology f)
    (fun _ ↦ inferInstance) P R hP hR

private theorem ordinary_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1, u + 1} A)) :
    (EtaleChartComparison.scalarSheafIso.{u} f X).hom.app (M ⊗ N) ≫
      (finiteVerdierOrdinaryExtension.{u} (Scheme.ProEt.topology X) f).map
        (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} A) X) M N) ≫
      Functor.OplaxMonoidal.δ (finiteVerdierOrdinaryExtension.{u}
        (Scheme.ProEt.topology X) f) _ _ =
    (ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} B) X).map
        (Functor.OplaxMonoidal.δ (finiteVerdierOrdinaryExtension.{u}
          X.smallEtaleTopology f) M N) ≫
      Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} B) X) _ _ ≫
      ((EtaleChartComparison.scalarSheafIso.{u} f X).hom.app M ⊗ₘ
        (EtaleChartComparison.scalarSheafIso.{u} f X).hom.app N) := by
  let : (finiteVerdierOrdinaryAdjunction.{u} X.smallEtaleTopology f).IsMonoidal :=
    isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  let : (finiteVerdierOrdinaryAdjunction.{u} (Scheme.ProEt.topology X) f).IsMonoidal :=
    isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  have hm := Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    X.toProEt X.smallEtaleTopology (Scheme.ProEt.topology X)
    (A := ModuleCat.{u + 1, u + 1} B) (ModuleCat.restrictScalars.{u + 1} f)
  let e := Functor.sheafPushforwardContinuousCompSheafComposeIso
    X.toProEt X.smallEtaleTopology (Scheme.ProEt.topology X)
    (A := ModuleCat.{u + 1, u + 1} B) (ModuleCat.restrictScalars.{u + 1} f)
  have : NatTrans.IsMonoidal e.inv := inferInstance
  have hd' := conjugateEquiv_symm_app_tensor_comp_δ
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1, u + 1} A) X).comp
      (finiteVerdierOrdinaryAdjunction.{u} (Scheme.ProEt.topology X) f))
    ((finiteVerdierOrdinaryAdjunction.{u} X.smallEtaleTopology f).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1, u + 1} B) X))
    e.inv M N
  have he : (EtaleChartComparison.scalarSheafIso.{u} f X).hom =
      (conjugateEquiv
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1, u + 1} A) X).comp
          (finiteVerdierOrdinaryAdjunction.{u} (Scheme.ProEt.topology X) f))
        ((finiteVerdierOrdinaryAdjunction.{u} X.smallEtaleTopology f).comp
          (ProEtale.comparisonAdjunction (ModuleCat.{u + 1, u + 1} B) X))).symm e.inv := by
    rfl
  rw [he]
  simpa only [Functor.OplaxMonoidal.comp_δ, Functor.comp_obj, Category.assoc] using hd'

private instance proSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _

private theorem generic_site_delta
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    letI := ProEtale.siteComparisonDerivedMonoidal C X
    Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar C X).mapDerivedCategory K M =
      (((ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison.app K).app M) := by
  exact (ProEtale.siteComparisonTensorIso_hom_app C X K M).symm.trans
    (canonical_site_tensor_agreement C X K M).symm

private theorem generic_site_tensor_normalization
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat] :
    let F := ProEtale.comparisonUpperStar C X
    Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := F.mapHomologicalComplex (.up ℤ))
      ((ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison)
      (fun P ↦ F.mapDerivedCategoryFactors.hom.app P) := by
  exact exact_site_normalization (ProEtale.comparisonUpperStar C X)

private theorem exact_representative_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change _ = F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]

/-- The balanced comparison carries the canonical strong-monoidal structures.
Source: Stacks Tags 03EL and 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
The proof is the K-flat representative tensor calculation for the published comparison iso. -/
theorem finiteCoefficientSiteComparison_isMonoidal
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) :
    letI : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
    letI : (finiteSiteComparisonPullback X B).Monoidal :=
      AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
        (ModuleCat.{u + 1} B) X
    letI : (finiteSiteComparisonPullback X A).Monoidal :=
      AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
        (ModuleCat.{u + 1} A) X
    letI : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
    NatTrans.IsMonoidal (finiteCoefficientSiteComparison X f).hom := by
  sorry

/-- The balanced scalar associator on the etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteEtaleCoefficientComposition
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    finiteEtaleCoefficientExtension X f ⋙ finiteEtaleCoefficientExtension X g ≅
      finiteEtaleCoefficientExtension X (g.comp f) :=
  AlgebraicGeometry.CoefficientScalarRepresentatives.composition X.smallEtaleTopology f g

/-- The balanced scalar associator on the pro-etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteProEtaleCoefficientComposition
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    finiteProEtaleCoefficientExtension X f ⋙ finiteProEtaleCoefficientExtension X g ≅
      finiteProEtaleCoefficientExtension X (g.comp f) :=
  AlgebraicGeometry.CoefficientScalarRepresentatives.composition
    (Scheme.ProEt.topology X) f g

/-- The h-tower equation for the concrete maps `f`, `g`, and `g.comp f`.
Source: Stacks Project, Tag 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
The two displayed associators are the balanced scalar associators on the etale and
pro-etale sites; the equation is the objectwise coherence equation in the successive
Hom-transport predicate.
-/
def FiniteCoefficientSiteTowerEquation
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : Prop :=
  let αet := finiteEtaleCoefficientComposition X f g
  let αpro := finiteProEtaleCoefficientComposition X f g
  let hAB := finiteCoefficientSiteComparison X f
  let hBC := finiteCoefficientSiteComparison X g
  let hAC := finiteCoefficientSiteComparison X (g.comp f)
  ∀ T : finiteEtaleDerivedCategory X A,
    (finiteSiteComparisonPullback X C).map (αet.inv.app T) ≫
        hBC.hom.app ((finiteEtaleCoefficientExtension X f).obj T) ≫
        (finiteProEtaleCoefficientExtension X g).map (hAB.hom.app T) ≫
        αpro.hom.app ((finiteSiteComparisonPullback X A).obj T) =
      hAC.hom.app T

/-- The successive Hom equations for the concrete coefficient maps `f` and `g`.
The two equations use the balanced etale and pro-etale coefficient compositors directly; there
are no arbitrary further functors and no invertibility guards.  The identity clause explicitly
uses `RingHom.id` and the identity functor unitor.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
def FiniteCoefficientSuccessiveHomLaws
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : Prop :=
  let F := finiteEtaleCoefficientExtension X f
  let FBC := finiteEtaleCoefficientExtension X g
  let FAC := finiteEtaleCoefficientExtension X (g.comp f)
  let G := finiteProEtaleCoefficientExtension X f
  let GBC := finiteProEtaleCoefficientExtension X g
  let GAC := finiteProEtaleCoefficientExtension X (g.comp f)
  let αet := finiteEtaleCoefficientComposition X f g
  let αpro := finiteProEtaleCoefficientComposition X f g
  letI : F.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology f
  letI : FBC.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology g
  letI : FAC.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology (g.comp f)
  letI : G.Monoidal := finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
  letI : GBC.Monoidal := finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) g
  letI : GAC.Monoidal :=
    finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) (g.comp f)
  letI : (finiteEtaleCoefficientExtension X (RingHom.id A)).Monoidal :=
    finiteCoefficientScalarMonoidal X.smallEtaleTopology (RingHom.id A)
  letI : (finiteProEtaleCoefficientExtension X (RingHom.id A)).Monoidal :=
    finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) (RingHom.id A)
  (FiniteCoefficientSiteTowerEquation X f g) ∧
    (∀ (K M : finiteEtaleDerivedCategory X A),
      internalHomComparison FAC K M ≫
          internalHomTransport αet.symm K M =
        αet.symm.hom.app (K ⟶[finiteEtaleDerivedCategory X A] M) ≫
          FBC.map (internalHomComparison F K M) ≫
          internalHomComparison FBC (F.obj K) (F.obj M)) ∧
    (∀ (K M : finiteProEtaleDerivedCategory X A),
      internalHomComparison GAC K M ≫
          internalHomTransport αpro.symm K M =
        αpro.symm.hom.app (K ⟶[finiteProEtaleDerivedCategory X A] M) ≫
          GBC.map (internalHomComparison G K M) ≫
          internalHomComparison GBC (G.obj K) (G.obj M)) ∧
    (∀ (K M : finiteEtaleDerivedCategory X A),
      let ι := RingHom.id A
      let Eι := finiteEtaleCoefficientExtension X ι
      let l := finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)
      internalHomComparison Eι K M ≫ internalHomTransport l K M =
        l.hom.app (K ⟶[finiteEtaleDerivedCategory X A] M)) ∧
    (finiteEtaleCoefficientComposition X (RingHom.id A) (RingHom.id A) ≪≫
        finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A) =
      Functor.isoWhiskerLeft (finiteEtaleCoefficientExtension X (RingHom.id A))
          (finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)) ≪≫
        Functor.rightUnitor (finiteEtaleCoefficientExtension X (RingHom.id A)) ≪≫
        finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)) ∧
    (∀ (K M : finiteProEtaleDerivedCategory X A),
      let ι := RingHom.id A
      let Eι := finiteProEtaleCoefficientExtension X ι
      let l := finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A)
      internalHomComparison Eι K M ≫ internalHomTransport l K M =
        l.hom.app (K ⟶[finiteProEtaleDerivedCategory X A] M)) ∧
    (finiteProEtaleCoefficientComposition X (RingHom.id A) (RingHom.id A) ≪≫
        finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A) =
      Functor.isoWhiskerLeft (finiteProEtaleCoefficientExtension X (RingHom.id A))
          (finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A)) ≪≫
        Functor.rightUnitor (finiteProEtaleCoefficientExtension X (RingHom.id A)) ≪≫
        finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A))


/-- Finite coefficient scalar/site descent and evaluation compatibility.

Source: Stacks Project, Tags 07A4 and 08J9;
(blueprint: lem-coef-finite-hom-site-equation-descent), final paragraph.  The parameters are a
finite or algebraically closed field of characteristic `p`, distinct primes `p` and `ell`,
a positive exponent `N`, arbitrary finite commutative rings `A`, `B`, and `C` killed by
`ell ^ N`, ring maps `f` and `g`, and a separated finite-type `k`-scheme `X` over `Spec k`.
The conclusion uses the concrete ordinary unbounded derived categories of constant-coefficient
module sheaves on `X_et` and `X_proet`; its four functors are fixed coefficient derived
extensions and derived comparison inverse images, and its comparison is the balanced
K-flat representative iso `finiteCoefficientSiteComparison`.

The postponed proof has eight steps. (1) Choose flat-term K-flat resolutions and define the
balanced comparison independently of the resolution. (2) Check its tensor equation using the
K-flat tensor-pullback comparisons. (3) Check associators, unitors and signed symmetry.
(4) Define the four transpose maps by the closed tensor-Hom adjunction and prove their
transpose equation. (5) Prove naturality, internal-Hom composition and identity by uniqueness
of transpose. (6) Transport the etale/pro-etale Hom square through the tensor equation.
(7) Apply the same representative calculation to the balanced scalar tower `f`, `g`, and
`g.comp f`, including the two scalar associators. (8) Apply the identity tensorators to
the scalar unitors and retain the successive Hom equation and the identity unitors.
-/
theorem finiteCoefficientSiteEquationDescent
    (p ell N : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hpell : ell ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (C : Type (u + 1)) [CommRing C] [Finite C]
    (hN : 0 < N)
    (hNA : ((ell ^ N : ℕ) : A) = 0)
    (hNB : ((ell ^ N : ℕ) : B) = 0)
    (hNC : ((ell ^ N : ℕ) : C) = 0)
    (f : A →+* B) (g : B →+* C)
    (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] :
    letI : BraidedCategory (finiteEtaleDerivedCategory X A) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteEtaleDerivedCategory X B) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteProEtaleDerivedCategory X A) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteProEtaleDerivedCategory X B) :=
      DerivedCategory.braidedCategory' _
    FiniteCoefficientSiteEquationLaws
        (finiteEtaleCoefficientExtension X f)
        (finiteProEtaleCoefficientExtension X f)
        (finiteSiteComparisonPullback X A)
        (finiteSiteComparisonPullback X B)
        (finiteCoefficientSiteComparison X f)
        (finiteCoefficientScalarMonoidal X.smallEtaleTopology f)
        (finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f)
        (AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
          (ModuleCat.{u + 1} A) X)
        (AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
          (ModuleCat.{u + 1} B) X)
        (finiteCoefficientSiteComparison_isMonoidal X f)
        (FiniteCoefficientSuccessiveHomLaws X f g) ∧
      FiniteCoefficientSiteTowerEquation X f g := by
  sorry

end WeilConjectures
