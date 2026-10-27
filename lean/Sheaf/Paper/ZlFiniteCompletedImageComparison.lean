/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.SfConstructibleHeart
import all Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteFpProEtalePushforwardExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.SfIntegralDirectImageConstructible
import all Sheaf.Paper.SfCompleteDirectImageReduction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.CharP.CharAndCard

/-! # Normalized completed finite direct image

Source: Stacks Tag 09A8; Bhatt--Scholze, Proposition 3.5.1 and Lemmas 3.5.6, 6.7.2
(blueprint: lem-zl-finite-completed-image-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The prescribed finite-image projection: direct image of the actual reduction unit,
followed by the resolution-normalized scalar square. This is real map data, not a
choice of a cone lift in a bare triangulated category.
Source: Stacks 0D6E; Bhatt--Scholze 3.5.6
(blueprint: lem-zl-finite-completed-image-comparison). -/
def zlFiniteCompletedImageProjection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    [HasProduct (sfDirectImageTerm l E f K)] :
    (sfCompletedDerivedDirectImage l E f).obj K ⟶ ∏ᶜ (sfDirectImageTerm l E f K) :=
  Pi.lift (fun n ↦
    (sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The finite-image comparison data, keeping the canonical resolution comparison and
all Roos projections. The auxiliary functors are required to be the termwise functors
by their localization comparisons; they are not arbitrary functors with the same objects.
Source: Stacks 09A8; Bhatt--Scholze 3.5.1, 3.5.6 and 6.7.2
(blueprint: lem-zl-finite-completed-image-comparison). -/
structure ZlFiniteCompletedImageComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  noetherian_source : IsNoetherian X
  noetherian_target : IsNoetherian Y
  dimension_source : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)
  dimension_target : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞)
  finitePresentation : LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f
  exactLimits : PreservesFiniteLimits (sfCompletedModuleDirectImage l E f)
  exactColimits : PreservesFiniteColimits (sfCompletedModuleDirectImage l E f)
  products : ∀ M : ℕ → scalarReductionSource l E X,
    IsIso (piComparison (sfCompletedModuleDirectImage l E f) M)
  finiteExact : ∀ n : ℕ,
    PreservesFiniteLimits (Scheme.proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))) ∧
    PreservesFiniteColimits (Scheme.proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)))
  finiteResolution : ∀ (n : ℕ)
    (P : CochainComplex (scalarReductionTarget l E X n) ℤ),
    IsIso ((Scheme.proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctorUnitQ P)
  scalarComparison : ∀ (n : ℕ) (M : scalarReductionTarget l E X n) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)),
    ((sfDirectImageRestrictionComparison l E f n).hom.app M).val.app U x = x
  derived : DerivedCategory (scalarReductionSource l E X) ⥤
    DerivedCategory (scalarReductionSource l E Y)
  factors : DerivedCategory.Q ⋙ derived ≅
    (sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  [commShift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  comparison : derived ≅ sfCompletedDerivedDirectImage l E f
  resolutionNormalization : ∀ P : CochainComplex (scalarReductionSource l E X) ℤ,
    factors.hom.app P ≫ (sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnitQ P =
      comparison.hom.app (DerivedCategory.Q.obj P)
  [derivedProducts : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y))]
  boundary : ∀ K : sfIntegralConstructibleCategory l E X,
    (∏ᶜ (sfDirectImageTerm l E f K.obj)) ⟶
      ((sfCompletedDerivedDirectImage l E f).obj K.obj)⟦(1 : ℤ)⟧
  roos : ∀ K : sfIntegralConstructibleCategory l E X,
    IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
      ((sfCompletedDerivedDirectImage l E f).obj K.obj)
      (zlFiniteCompletedImageProjection l E f K.obj) (boundary K)
  normalization : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    comparison.hom.app K.obj ≫ zlFiniteCompletedImageProjection l E f K.obj ≫
        Pi.π (sfDirectImageTerm l E f K.obj) n =
      derived.map ((sfDerivedReductionUnit l E X n).app K.obj) ≫
        comparison.hom.app ((sfDerivedReductionRestricted l E X n).obj K.obj) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K.obj)
  constructible : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((sfCompletedDerivedDirectImage l E f).obj K.obj)
  complete : ∀ K : sfIntegralConstructibleCategory l E X,
    IsSfDerivedComplete l E Y ((sfCompletedDerivedDirectImage l E f).obj K.obj)
  reduction : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    IsIso (sfDirectImageReductionComparison l E f
      { obj := (sfCompletedDerivedDirectImage l E f).obj K.obj,
        projection := zlFiniteCompletedImageProjection l E f K.obj, boundary := boundary K,
        roos := roos K } n)
  etaleOrigin : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    ∃ L : Etale.DerivedCategoryModule
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) X,
      @Etale.DerivedCategory.isBoundedConstructible _ _
        (@Finite.of_equiv _ _
          (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))
          Equiv.ulift.symm) X L ∧
      Nonempty (((Scheme.proEtaleModuleRestriction X
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj
          ((scalarReductionDerivedExtension l E X n).obj K.obj) ≅
        (Functor.mapDerivedCategory
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) X)).obj L)
  restricts : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y (derived.obj K.obj)
  standard : ∀ (K : sfIntegralConstructibleCategory l E X) (nonpositive : Bool),
    sfIntegralStandardClass l E X nonpositive 0 K →
      ∀ h : sfIntegralConstructible l E Y (derived.obj K.obj),
        sfIntegralStandardClass l E Y nonpositive 0 ⟨derived.obj K.obj, h⟩

/-- The natural comparison to the specified tower-limit model. Its components are the
canonical resolution comparison of the termwise exact image, restricted to the
constructible category; the Roos field identifies its target with the required limit.
Source: Stacks 09A8; Bhatt--Scholze 3.5.6
(blueprint: lem-zl-finite-completed-image-comparison). -/
def ZlFiniteCompletedImageComparison.theta
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : ZlFiniteCompletedImageComparison l E f) :
    (sfIntegralConstructible l E X).ι ⋙ C.derived ≅
      (sfIntegralConstructible l E X).ι ⋙ sfCompletedDerivedDirectImage l E f :=
  Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι C.comparison

private theorem finite_module_exact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (a : RY ⟶ (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RX) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1}
      (F := Scheme.proEtaleBaseChange f)
      (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
      (S := (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩) ∧
    PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1}
      (F := Scheme.proEtaleBaseChange f)
      (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
      (S := (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩) := by
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have h := (Scheme.finite_fp_proEtale_pushforward_exact f).2.2 RY RX
    ((adj.homEquiv RY RX).symm a)
  have ha : (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a =
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
    ext U x
    rfl
  simpa only [adj, Equiv.apply_symm_apply, ha] using h

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem finite_comparison
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsFinite f] :
    Nonempty (ZlFiniteCompletedImageComparison l E f) := by
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := {}
  let : IsNoetherian Y := {}
  have hfp := finitePresentation_of_finite_over_locallyNoetherian f
  let := hfp.1
  let F := sfCompletedModuleDirectImage l E f
  have hF := finite_module_exact f
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X) (sfCompletedCoefficientMap l E f)
  let : PreservesFiniteLimits F := hF.1
  let : PreservesFiniteColimits F := hF.2
  have hn (n : ℕ) := finite_module_exact f
    (Scheme.proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))
    (Scheme.proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))
    (Scheme.proEtaleCoefficientDirectImageMap f
      (Padic.coefficientExtensionRing l E (n + 1)))
  have hunit (P : CochainComplex (scalarReductionSource l E X) ℤ) :
      IsIso (F.rightDerivedFunctorUnitQ P) := by
    unfold Functor.rightDerivedFunctorUnitQ
    infer_instance
  let factors : DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      let := hunit P
      exact (asIso (F.rightDerivedFunctorUnitQ P)).symm)
      (fun a ↦ by
        apply (cancel_mono (F.rightDerivedFunctorUnitQ _)).1
        simp only [Category.assoc, Iso.symm_hom, asIso_inv,
          IsIso.inv_hom_id, Category.comp_id]
        dsimp only [Functor.comp_map]
        rw [F.rightDerivedFunctorUnitQ_naturality]
        simp)
  let : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y)) := by
    let A := scalarReductionSource l E Y
    let : HasCountableProducts A := inferInstance
    let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
    let : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
      { preserves := by
          intro M N a ha
          have h := (Scheme.ProEt.countableProducts_exact.{u, u, 0} Y
            (completedIntegralCommRingSheafUnrestricted l E Y)).2.2
            ℕ (fun n ↦ M.obj ⟨n⟩) (fun n ↦ N.obj ⟨n⟩)
            (fun n ↦ a.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map a = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ a.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    let := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
    let := CountableAB4Star.of_hasExactLimitsOfShape_nat A
    exact (derivedCategory_countableProducts_core.{0} A).choose
  let := completed_derived_products l E f
  have hroos (K : sfIntegralConstructibleCategory l E X) :
      ∃ δ, IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
        ((sfCompletedDerivedDirectImage l E f).obj K.obj)
        (zlFiniteCompletedImageProjection l E f K.obj) δ := by
    let G := sfCompletedDerivedDirectImage l E f
    let a (n : ℕ) := (sfDerivedRestrictionComparison l E f n).app
      ((scalarReductionDerivedExtension l E X n).obj K.obj)
    obtain ⟨hp, δ, hδ⟩ := K.property.1
    let := hp
    let : HasProduct (fun n ↦ G.obj ((sfDerivedReductionRestricted l E X n).obj K.obj)) :=
      hasProduct_of_equiv_of_iso (sfDirectImageTerm l E f K.obj) _ (Equiv.refl ℕ) a
    obtain ⟨ε, hε⟩ := map_roos G
      (fun n ↦ (sfDerivedReductionTransition l E X n).app K.obj) K.obj
      (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app K.obj)) δ hδ
    let p (n : ℕ) := G.map ((sfDerivedReductionUnit l E X n).app K.obj) ≫ (a n).hom
    have hR : ∃ hp : HasProduct (sfDirectImageTerm l E f K.obj), letI := hp
        ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
          (G.obj K.obj) (Pi.lift p) ε := by
      apply roos_transport
        (X := fun n ↦ G.obj ((sfDerivedReductionRestricted l E X n).obj K.obj))
        (Y := sfDirectImageTerm l E f K.obj)
        (fun n ↦ G.map ((sfDerivedReductionTransition l E X n).app K.obj))
        (sfDirectImageTransition l E f K.obj) (Iso.refl (G.obj K.obj)) a
        (fun n ↦ G.map ((sfDerivedReductionUnit l E X n).app K.obj)) p
      · intro n
        dsimp only [sfDirectImageTransition, a, Iso.app_hom, Iso.app_inv]
        simp only [Iso.hom_inv_id_app_assoc]
        rfl
      · intro n
        simp only [p, Iso.refl_hom, Category.id_comp]
      · refine ⟨inferInstance, ε, ?_⟩
        simpa only [Pi.lift_π] using hε
    obtain ⟨hp', ε', hε'⟩ := hR
    have hR' : ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
        (G.obj K.obj) (Pi.lift p) ε := by
      simpa only using (show ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
        (G.obj K.obj) (Pi.lift p) ε from ⟨ε', hε'⟩)
    simpa only [p, G, a, Iso.app_hom, zlFiniteCompletedImageProjection] using hR'
  let boundary := fun K ↦ (hroos K).choose
  let L (K : sfIntegralConstructibleCategory l E X) : SfIntegralDirectImage l E f K.obj :=
    { obj := (sfCompletedDerivedDirectImage l E f).obj K.obj
      projection := zlFiniteCompletedImageProjection l E f K.obj
      boundary := boundary K
      roos := (hroos K).choose_spec }
  have hc (K : sfIntegralConstructibleCategory l E X) :=
    (sfIntegralDirectImage_constructible k l hl E f K.obj K.property).2.1 (L K)
  refine ⟨{
    noetherian_source := inferInstance
    noetherian_target := inferInstance
    dimension_source := exists_topologicalKrullDim_le (X ↘ Spec (.of k))
    dimension_target := exists_topologicalKrullDim_le (Y ↘ Spec (.of k))
    finitePresentation := hfp
    exactLimits := hF.1
    exactColimits := hF.2
    products := ?_
    finiteExact := hn
    finiteResolution := ?_
    scalarComparison := (fun n ↦
      (sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose_spec)
    derived := F.rightDerivedFunctor
    factors := factors
    triangulated := inferInstance
    comparison := Iso.refl _
    resolutionNormalization := ?_
    boundary := boundary
    roos := fun K ↦ (hroos K).choose_spec
    normalization := ?_
    constructible := fun K ↦ (hc K).1
    complete := fun K ↦ (hc K).2.1
    reduction := fun K n ↦ (hc K).2.2.1 n
    etaleOrigin := ?_
    restricts := fun K ↦ (hc K).1
    standard := ?_ }⟩
  · intro M
    have h := (Scheme.proEtaleRingModuleAdjunction f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (coefficient_inverse_image_iso l E f)).rightAdjoint_preservesLimits
    rw [completed_direct_image_eq l E f] at h
    let := h
    infer_instance
  · intro n P
    let : PreservesFiniteLimits (Scheme.proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))) := (hn n).1
    let : PreservesFiniteColimits (Scheme.proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))) := (hn n).2
    unfold Functor.rightDerivedFunctorUnitQ
    infer_instance
  · intro P
    exact IsIso.inv_hom_id _
  · intro K n
    simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp,
      zlFiniteCompletedImageProjection, Pi.lift_π]
    rfl
  · intro K n
    let B := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let R := Scheme.proEtaleModuleRestriction X B
    let V := (scalarReductionDerivedExtension l E X n).obj K.obj
    obtain ⟨a, b, hab, hV⟩ := K.property.2
    have hc (i : ℤ) : ProEtale.IsConstructible (ULift.{u + 1} B)
        ((DerivedCategory.homologyFunctor _ i).obj (R.mapDerivedCategory.obj V)) := by
      have hc := (Scheme.proEtaleModuleRestriction_constructible_iff X B _).mp
        ((hV n).1.2 i)
      exact ProEtale.isConstructible_of_iso
        ((R.mapDerivedCategoryHomologyFunctorIso i).app V) hc
    have hz (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (R.mapDerivedCategory.obj V)) := by
      apply R.isZero_homologyFunctor_mapDerivedCategory_obj
      by_contra hz
      have hv := (hV n).2 hz
      have hia : a ≤ i := hv.1
      have hib : i ≤ b := hv.2
      rcases hi with hi | hi <;> omega
    obtain ⟨T, hT, ⟨eT⟩⟩ := ProEtale.fixedDerivedOrigin X (ULift.{u + 1} B)
      (R.mapDerivedCategory.obj V) hc a b hz
    exact ⟨T, hT, ⟨eT.symm⟩⟩
  · intro K nonpositive hK h i hi
    exact F.isZero_homologyFunctor_mapDerivedCategory_obj (hK i hi) |>.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        (F.rightDerivedFunctorIsoMapDerivedCategory.app K.obj))

/-- Finite completed direct image is its normalized reduction-tower direct image,
including the identical assertion for every finite geometric fibre.
Source: Stacks 09A8; Bhatt--Scholze 3.5.1, 3.5.6 and 6.7.2
(blueprint: lem-zl-finite-completed-image-comparison).

Proof:
1. Finite type over the field gives Noetherian schemes and finite dimension
(lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type).
Finite maps over a locally Noetherian target are finitely presented
(pqf-lem-finite-fp-locnoeth). Finite base change gives the same hypotheses for h
(lem-weil-pbc-finite-morphism-permanence).
2. Apply lem-zl-finite-fp-proetale-pushforward-exact to the completed and each
finite coefficient ring. The exact-functor derived triangulated and derived-functor
lemmas identify the termwise functor and its canonical resolution comparison.
3. Products are sectionwise (lem-weil-pbc-module-sheaves-limits-sectionwise).
Both scalar-restriction/direct-image composites have the same sections and actions,
by the finite projection equation for sfCompletedCoefficientMap. Their identification
is identity on sections and commutes with each coefficient quotient transition.
4. On a flat-term K-flat representative take the strict quotient tower and its
actual augmentation x mapped to x tensor 1. The coefficient hypotheses follow from
lem-sf-bc-adic-ring-domain. The canonical-unit implication of
lem-pur-roos-intrinsic-completeness-equivalence makes the augmentation invertible;
lem-weil-strict-roos-comparison identifies its projections with the reduction units.
5. Countable products are exact by lem-weil-proetale-countable-products-exact.
Apply lem-cbc-exact-product-functor-strict-limit to that strict tower and its
augmentation, after applying the termwise direct image. Its comparison composed
with direct image of the completion unit is theta. The identity-on-sections scalar
comparison identifies every term and transition with sfDirectImageTerm and
sfDirectImageTransition. To check the latter, choose K-injective resolutions at
both coefficient levels: the second resolution comparison factors through the
restriction of the first. The inverse comparison of
lem-weil-proetale-direct-image-restriction-of-scalars cancels that second factor.
The strict augmentation clause now gives precisely normalization; localization
gives naturality in K and independence of the chosen representative.
6. lem-sf-integral-direct-image-constructible gives constructibility, completeness,
and invertibility of the actual scalar-adjoint reduction comparison.
lem-sf-proetale-constructible-origin identifies each intrinsically constructible
reduction with a bounded constructible etale complex through the site comparison.
7. Exact functors commute with cohomology
(lem-weil-pbc-exact-functor-complex-cohomology). Thus positive and negative
cohomology vanishing are preserved, which is standard for both Bool values.
Every step applies as well to the finite base change h, including empty fibres. -/
theorem zlFiniteCompletedImageComparison (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] :
    Nonempty (ZlFiniteCompletedImageComparison l E f.left) ∧
      ∀ s : Over.mk (𝟙 (Spec (.of D.k))) ⟶ Y,
        IsFinite (pullback.snd f.left s.left) ∧
        Nonempty (ZlFiniteCompletedImageComparison l E (pullback.snd f.left s.left)) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (l : D.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : l.Prime) _hl.symm)
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  let : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  let : f.left.IsOver (Spec (.of D.k)) := ⟨f.w⟩
  refine ⟨finite_comparison D.k l hunit E f.left, ?_⟩
  intro s
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : (pullback f.left s.left).Over (Spec (.of D.k)) :=
    ⟨pullback.snd f.left s.left⟩
  let : (pullback.snd f.left s.left).IsOver (Spec (.of D.k)) := ⟨by
    change pullback.snd f.left s.left ≫ 𝟙 _ = pullback.snd f.left s.left
    exact Category.comp_id _⟩
  let : LocallyOfFiniteType (pullback f.left s.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left s.left))
  let : QuasiCompact (pullback f.left s.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd f.left s.left))
  let : LocallyOfFiniteType (Spec (.of D.k) ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  let : QuasiCompact (Spec (.of D.k) ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  exact ⟨inferInstance, finite_comparison D.k l hunit E
    (X := pullback f.left s.left) (Y := Spec (.of D.k)) (pullback.snd f.left s.left)⟩

end WeilConjectures
