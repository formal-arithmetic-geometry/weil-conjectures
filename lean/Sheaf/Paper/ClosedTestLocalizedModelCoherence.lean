/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestLocalizedModelData
import Sheaf.Paper.ClosedTestComparisonTestNaturality
import Sheaf.Paper.ClosedTestLocalizedRestrictionNormalization
import Sheaf.Paper.ClosedTestDerivedComparisonNormalization
import Sheaf.Paper.ClosedTestGeometricSectionCoherence
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Resolution and localization coherence of closed-test section models
Source: Stacks Tags 070I, 0D6E, 0D6G and 09BL
(blueprint: lem-sfb-closed-test-localized-model-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
open ClosedTestDerivedExchangeModel
-- Compare with the canonical instances used by the existing section models.
attribute [-instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal ClosedTestDerivedExchangeModel.moduleAbelian
  ClosedTestDerivedExchangeModel.moduleSectionsAdditive
attribute [instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (A : Type u) [CommRing A] (𝔞 : Ideal A)
variable {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ 𝔞)))
  (w : IsPullback h fZ f (closedMap A 𝔞))




private theorem paste_square {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} {a : X₁ ⟶ X₂} {b : Y₁ ⟶ Y₂} {c : Z₁ ⟶ Z₂}
    {u : X₁ ⟶ Y₁} {u' : X₂ ⟶ Y₂} {v : Y₁ ⟶ Z₁} {v' : Y₂ ⟶ Z₂}
    (h₁ : a ≫ u' = u ≫ b) (h₂ : b ≫ v' = v ≫ c) :
    a ≫ (u' ≫ v') = (u ≫ v) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private theorem homotopy_of_Q_eq
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P H : CochainComplex C ℤ} [H.IsKInjective]
    (a b : P ⟶ H) (hab : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    Nonempty (Homotopy a b) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ H).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app H)).mp
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, hab]

private theorem localizationUnit_naturality {Y : Scheme.{u}} (W : Y.ProEt)
    {I I' : CochainComplex (Modules Λ Y) ℤ} (a : I ⟶ I') :
    DerivedCategory.Q.map ((sections Λ W).map a) ≫ localizationUnit Λ W I' =
      localizationUnit Λ W I ≫ (sectionsOver Λ W.hom).map (DerivedCategory.Q.map a) := by
  exact (localizationTransformation Λ W).naturality a

private theorem sourceUnit_naturality (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    {I I' : CochainComplex (Modules Λ X) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (a : I ⟶ I') :
    DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map a) ≫
        sourceUnit Λ A 𝔞 f V I' =
      sourceUnit Λ A 𝔞 f V I ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
          (ev Λ (test A 𝔞 V)).rightDerivedFunctor).map (DerivedCategory.Q.map a) := by
  unfold sourceUnit
  exact (sourceTransformation Λ A 𝔞 f V).naturality a

private theorem representatives_exist
    {I I' : CochainComplex (Modules Λ X) ℤ} [I'.IsKInjective]
    {J J' : CochainComplex (Modules Λ XZ) ℤ} [J'.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J')
    [QuasiIso j] [QuasiIso j']
    (α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I') :
    ∃ (a : I ⟶ I') (b : J ⟶ J'), Represents Λ h j j' α a b := by
  obtain ⟨a, ha⟩ := CochainComplex.IsKInjective.exists_Q_map_eq I I' α
  obtain ⟨b, hb⟩ := CochainComplex.IsKInjective.exists_Q_map_eq J J'
    ((asIso (DerivedCategory.Q.map j)).inv ≫
      DerivedCategory.Q.map
        (((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map j')
  exact ⟨a, b, ha, hb⟩

private theorem representatives_homotopy
    {I I' : CochainComplex (Modules Λ X) ℤ}
    {J J' : CochainComplex (Modules Λ XZ) ℤ} [J'.IsKInjective]
    {j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J}
    {j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J'}
    [QuasiIso j] [QuasiIso j']
    {α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I'}
    {a : I ⟶ I'} {b : J ⟶ J'} (hab : Represents Λ h j j' α a b) :
    Nonempty (Homotopy (j ≫ b)
      (((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).map a ≫ j')) := by
  apply homotopy_of_Q_eq
  simp only [Functor.map_comp, hab.2, asIso_inv,
    IsIso.hom_inv_id_assoc]

private theorem evaluated_model_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory E]
    (P : C ⥤ D) (F : C ⥤ E) (G : D ⥤ E)
    [P.Additive] [F.Additive] [G.Additive] (τ : F ⟶ P ⋙ G)
    {I I' : CochainComplex C ℤ} {J J' : CochainComplex D ℤ}
    (a : I ⟶ I') (b : J ⟶ J')
    (j : (P.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (j' : (P.mapHomologicalComplex (.up ℤ)).obj I' ⟶ J')
    (H : Homotopy (j ≫ b) ((P.mapHomologicalComplex (.up ℤ)).map a ≫ j')) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I' ≫
          (G.mapHomologicalComplex (.up ℤ)).map j') =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I ≫
          (G.mapHomologicalComplex (.up ℤ)).map j) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map b) := by
  have he := DerivedCategory.Q_map_eq_of_homotopy _ (G.mapHomotopy H)
  have hn := (NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality a
  have hn' := congrArg (fun t ↦ DerivedCategory.Q.map t) hn
  simp only [Functor.map_comp] at hn' he ⊢
  exact paste_square hn' he.symm

private theorem modelArrow_naturality
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    {I I' : CochainComplex (Modules Λ X) ℤ}
    {J J' : CochainComplex (Modules Λ XZ) ℤ} [J'.IsKInjective]
    {j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J}
    {j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J'}
    [QuasiIso j] [QuasiIso j']
    {α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I'}
    {a : I ⟶ I'} {b : J ⟶ J'} (hab : Represents Λ h j j' α a b) :
    DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map a) ≫
        modelArrow Λ A 𝔞 f h fZ w V I' J' j' =
      modelArrow Λ A 𝔞 f h fZ w V I J j ≫
        DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map b) := by
  obtain ⟨H⟩ := representatives_homotopy Λ h hab
  exact evaluated_model_naturality (CondensedRing.upperStar Λ h)
    (ev Λ (sourceTest A 𝔞 f V)) (ev Λ (targetTest A 𝔞 fZ V))
    (unitAt Λ h (sourceTest A 𝔞 f V) (targetTest A 𝔞 fZ V)
      (fibreTestArrow A 𝔞 f h fZ w V)) a b j j' H

private theorem replacement_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {I I' : CochainComplex C ℤ} {J J' : CochainComplex D ℤ}
    (j : (P.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (j' : (P.mapHomologicalComplex (.up ℤ)).obj I' ⟶ J') [QuasiIso j] [QuasiIso j']
    (a : I ⟶ I') (b : J ⟶ J')
    (hb : DerivedCategory.Q.map b = (asIso (DerivedCategory.Q.map j)).inv ≫
      DerivedCategory.Q.map ((P.mapHomologicalComplex (.up ℤ)).map a) ≫
      DerivedCategory.Q.map j') :
    DerivedCategory.Q.map b ≫ (asIso (DerivedCategory.Q.map j')).inv ≫
        P.mapDerivedCategoryFactors.inv.app I' =
      ((asIso (DerivedCategory.Q.map j)).inv ≫ P.mapDerivedCategoryFactors.inv.app I) ≫
        P.mapDerivedCategory.map (DerivedCategory.Q.map a) := by
  rw [hb]
  simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  exact congrArg (inv (DerivedCategory.Q.map j) ≫ ·)
    (P.mapDerivedCategoryFactors.inv.naturality a)

private theorem targetUnit_naturality
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    {I I' : CochainComplex (Modules Λ X) ℤ}
    {J J' : CochainComplex (Modules Λ XZ) ℤ} [J.IsKInjective] [J'.IsKInjective]
    {j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J}
    {j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J'}
    [QuasiIso j] [QuasiIso j']
    {α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I'}
    {a : I ⟶ I'} {b : J ⟶ J'} (hab : Represents Λ h j j' α a b) :
    DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map b) ≫
        targetUnit Λ A 𝔞 h fZ V I' J' j' =
      targetUnit Λ A 𝔞 h fZ V I J j ≫
        (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
          (ev Λ (test A 𝔞 V)).rightDerivedFunctor).map α := by
  rcases hab with ⟨rfl, hb⟩
  have hn := (targetTransformation Λ A 𝔞 fZ V).naturality b
  simp only [Functor.comp_map] at hn
  let r := (asIso (DerivedCategory.Q.map j)).inv ≫
    (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I
  let r' := (asIso (DerivedCategory.Q.map j')).inv ≫
    (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I'
  have hr : DerivedCategory.Q.map b ≫ r' = r ≫ (pull Λ h).map (DerivedCategory.Q.map a) := by
    exact replacement_naturality (CondensedRing.upperStar Λ h) j j' a b hb
  have he := congrArg (fun q ↦
    (CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
      (ev Λ (test A 𝔞 V)).rightDerivedFunctor).map q) hr
  simp only [CategoryTheory.Functor.map_comp, Functor.comp_map] at he
  unfold targetUnit
  change DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map b) ≫
      (targetTransformation Λ A 𝔞 fZ V).app J' ≫
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
          ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).map r') =
    ((targetTransformation Λ A 𝔞 fZ V).app J ≫
      (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
        ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).map r)) ≫ _
  exact paste_square hn he

private theorem evaluation_map_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    {I I' : CochainComplex C ℤ} [I.IsKInjective] [I'.IsKInjective]
    (a : I ⟶ I') [IsIso (DerivedCategory.Q.map a)] :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a)) := by
  have : IsIso (F.rightDerivedFunctorUnitQ I) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have : IsIso (F.rightDerivedFunctorUnitQ I') := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have : IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
      F.rightDerivedFunctorUnitQ I') := by
    rw [F.rightDerivedFunctorUnitQ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorUnitQ I')

private theorem resolution_coherence
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : ResolutionCoherence Λ A 𝔞 f h fZ w V I J j := by
  intro K' I' _ e' J' _ j' _ α
  refine ⟨representatives_exist Λ h j j' α, ?_⟩
  intro a b hab
  refine ⟨representatives_homotopy Λ h hab,
    modelArrow_naturality Λ A 𝔞 f h fZ w V hab, ?_,
    targetUnit_naturality Λ A 𝔞 h fZ V hab, ?_,
    localizationUnit_naturality Λ (targetTest A 𝔞 fZ V) b, ?_, ?_, ?_⟩
  · simpa only [hab.1] using sourceUnit_naturality Λ A 𝔞 f V a
  · simpa only [hab.1] using
      localizationUnit_naturality Λ (sourceTest A 𝔞 f V) a
  · intro hα
    have ha : IsIso (DerivedCategory.Q.map a) := by rw [hab.1]; exact hα
    have hb : IsIso (DerivedCategory.Q.map b) := by
      rw [hab.2]
      have hp : IsIso (DerivedCategory.Q.map
          (((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).map a)) := by
        exact evaluation_map_isIso (CondensedRing.upperStar Λ h) a
      infer_instance
    exact ⟨evaluation_map_isIso (ev Λ (sourceTest A 𝔞 f V)) a,
      evaluation_map_isIso (ev Λ (targetTest A 𝔞 fZ V)) b⟩
  · intro a a' b b' hab hab'
    have ha : DerivedCategory.Q.map a = DerivedCategory.Q.map a' :=
      hab.1.trans hab'.1.symm
    refine ⟨homotopy_of_Q_eq a a' ha, homotopy_of_Q_eq b b' ?_⟩
    rw [hab.2, hab'.2]
    congr 2
    exact DerivedCategory.Q_map_eq_of_homotopy _
      ((CondensedRing.upperStar Λ h).mapHomotopy
        (homotopy_of_Q_eq a a' ha).some)
  · intro a a' b b' H H'
    exact ⟨DerivedCategory.Q_map_eq_of_homotopy _
        ((ev Λ (sourceTest A 𝔞 f V)).mapHomotopy H),
      DerivedCategory.Q_map_eq_of_homotopy _
        ((ev Λ (targetTest A 𝔞 fZ V)).mapHomotopy H')⟩

/-- Resolution independence, derived-morphism naturality and geometric coherence of the
specified closed-test section models. The source inverse uses the actual closed unit;
the other three comparisons use the direct-image and localized section identities.
No conclusion asserts invertibility of the closed restriction.

Source: Stacks Project, derived.tex Tag 070I, sites-cohomology.tex Tags 0D6E and 0D6G
(blueprint: lem-sfb-closed-test-localized-model-coherence).

Proof plan, following the eight steps of the DAG:
1. The exact internal/section-ring module equivalence preserves sections, resolutions
and actual adjunction maps (lem-sfb-closed-test-unit-evaluation). The four normalized
comparisons are those of lem-sfb-closed-test-kinjective-section-models.
2. Represent every derived morphism by the unique homotopy class into I', then into J'
using lem-sc-kinjective-quasi-iso-comparison. Injectivity with target J' gives the
homotopy j v ~ (h-star u) j'. Do not assume h-star I K-injective.
3. Evaluate this homotopy and naturality of the actual inverse-image unit. This gives
c r' = r d; homotopic representatives induce identical derived arrows. For an invertible
input morphism the two transitions are isomorphisms. Uniqueness gives identity and
composition laws.
4. Naturality of the universal right-derived units gives all four comparison squares
(def-sfb-right-derived-functor). Invert naturality of the actual closed unit. Exact
V-evaluation lets its resolution unit be inverted even on a non-K-injective complex.
5. The sheaf maps eta_h and j commute with presheaf restriction. Their slice unit
identifications give the test square (lem-sbc-ringed-topos-sheaf-slice-derived-comparison).
The inverse closed unit is test-natural by lem-sfb-closed-test-unit-evaluation.
6. For an isomorphism of squares use the unique unit-compatible left-adjoint comparison
(lem-weil-pbc-conjugate-iso-unit-equation and lem-exc-closed-site-adjunction).
7. Pro-etale localization is a slice (lem-weil-proetale-weakly-etale-localization).
The ringed-slice direct-image comparison is the degreewise section identity and the mate
of pullback composition, including the counit equation. Transpose to obtain its unit
equation; exact source restriction preserves K-injectives.
8. Apply these equations to h, then f,s,f_Z. Compose the unit section with restricted j;
all local resolution changes agree by steps 2-4. Arbitrary local tests use their own
closed lifts, not the base change of a previously chosen lift. Successive localizations
agree by the K-injective normalization of
lem-weil-pbc-ringed-topoi-derived-pushforward-composition. -/
theorem closed_test_localized_model_coherence [IsAffine X]
    (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V).left, ⊤)]
    (K : DerivedCategory.Plus (Modules Λ X))
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (_e : DerivedCategory.Q.obj I ≅ K.obj)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    IsIso (sourceUnit Λ A 𝔞 f V I) ∧
    IsIso (targetUnit Λ A 𝔞 h fZ V I J j) ∧
    IsIso (localizationUnit Λ (sourceTest A 𝔞 f V) I) ∧
    IsIso (localizationUnit Λ (targetTest A 𝔞 fZ V) J) ∧
    ResolutionCoherence Λ A 𝔞 f h fZ w V I J j ∧
    TestCoherence Λ A 𝔞 f h fZ w V I J j ∧
    LocalizedModelEquation Λ A 𝔞 f h fZ w V I J j ∧
    NormalizedComparisons Λ A 𝔞 f h fZ V I J j ∧
    GeometricCoherence Λ A 𝔞 f h fZ w V := by
  obtain ⟨hL, hR, hN⟩ :=
    closed_test_derived_comparison_normalization Λ A 𝔞 f h fZ V K I _e J j
  have hS : IsIso (sourceUnit Λ A 𝔞 f V I) := by
    obtain ⟨eC, eD, eV, hC, hD, _⟩ := hN
    rw [← hC]
    infer_instance
  have hT : IsIso (targetUnit Λ A 𝔞 h fZ V I J j) := by
    obtain ⟨eC, eD, eV, hC, hD, _⟩ := hN
    rw [← hD]
    infer_instance
  exact ⟨hS, hT, hL, hR, resolution_coherence Λ A 𝔞 f h fZ w V I J j,
    closed_test_comparison_test_naturality Λ A 𝔞 f h fZ w V I J j,
    closed_test_localized_restriction_normalization Λ A 𝔞 f h fZ w V I J j, hN,
    closed_test_geometric_section_coherence Λ A 𝔞 f h fZ w V⟩

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
