/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
public import Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit
public import Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.CategoryTheory.SystemEvaluationTopos
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.ClosedScalarHomComparison
public import Sheaf.Paper.CoefficientHomZeroClass
import Sheaf.CategoryTheory.ScalarHomZeroCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Finite projections of the enriched sequence adjunction

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6E;
agent uncurrying of the enriched finite projection, returned calculus step 14
(blueprint: lem-coef-enriched-sequence-projection-formula).

Index n denotes positive level n+1. We use the sequence-site realization of systems
and the recorded equivalence with strict semilinear systems to retain total-limit
projections and the strict derived-sections comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections
namespace SheafOfModules.EnrichedSequenceProjection

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Global sections as maps from the recorded rank-one module.
Source: Stacks 08JA (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev homSections (A : Sheaf J CommRingCat.{max c v r}) :
    sequenceCoefficientModules A ⥤ AddCommGrpCat.{max c v r} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)))

/-- The comparison of the two ordinary sections presentations is fixed on every section.
Source: Stacks 01FT, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: a limit element is a compatible family of sections. The unit-Hom equivalence
sends a map out of the rank-one module to its value on one. These inverse operations
preserve addition and commute with module maps. Equality of all section evaluations
makes the isomorphism unique. This also applies to the empty site. -/
theorem ordinarySectionsIso_exists (A : Sheaf J CommRingCat.{max c v r}) :
    ∃! ξ : sequenceCoefficientSections A ≅ homSections.{c, v, r} J A,
      ∀ (M : sequenceCoefficientModules A) (x : (sequenceCoefficientSections A).obj M)
        (U : Cᵒᵖ),
        (M.unitHomEquiv ((ξ.hom.app M) x)).val U =
          (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x := by
  let E (M : sequenceCoefficientModules A) :
      (sequenceCoefficientSections A).obj M ≃ (homSections.{c, v, r} J A).obj M :=
    (Types.isLimitEquivSections (isLimitOfPreserves
      (CategoryTheory.forget AddCommGrpCat.{max c v r})
      (limit.isLimit ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
        sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M)))).trans M.unitHomEquiv.symm
  have hE (M : sequenceCoefficientModules A) (x : (sequenceCoefficientSections A).obj M)
      (U : Cᵒᵖ) : (M.unitHomEquiv (E M x)).val U =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x := by
    exact congrArg (fun s : M.sections ↦ s.val U)
      (M.unitHomEquiv.apply_symm_apply _)
  let f (M : sequenceCoefficientModules A) :
      (sequenceCoefficientSections A).obj M ⟶ (homSections.{c, v, r} J A).obj M :=
    AddCommGrpCat.ofHom
      { toFun := E M
        map_zero' := by
          apply M.unitHomEquiv.injective
          ext U
          rw [hE]
          change (limit.π ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) U).hom 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          apply M.unitHomEquiv.injective
          ext U
          rw [hE]
          change (limit.π ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) U).hom (x + y) =
            ((E M x).val.app U) (1 : A.obj.obj U) +
              ((E M y).val.app U) (1 : A.obj.obj U)
          rw [← unitHomEquiv_apply_coe, ← unitHomEquiv_apply_coe, hE, hE]
          exact map_add _ x y }
  have hf (M : sequenceCoefficientModules A) : IsIso (f M) :=
    (ConcreteCategory.isIso_iff_bijective (f M)).mpr (E M).bijective
  let ξ : sequenceCoefficientSections A ≅ homSections.{c, v, r} J A :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (by
      intro M N g
      ext x
      apply N.unitHomEquiv.injective
      ext U
      change (N.unitHomEquiv (E N ((sequenceCoefficientSections A).map g x))).val U =
        (N.unitHomEquiv (E M x ≫ g)).val U
      rw [unitHomEquiv_comp_apply]
      rw [hE]
      change _ = (g.val.app U) ((M.unitHomEquiv (E M x)).val U)
      rw [hE]
      have hn := (lim.π U).naturality
        ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).map g)
      change (sequenceCoefficientSections A).map g ≫
          (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj N) =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) ≫
            ((CategoryTheory.forget₂ (ModuleCat (A.obj.obj U)) AddCommGrpCat).map
              (g.val.app U)) at hn
      exact ConcreteCategory.congr_hom hn x)
  refine ⟨ξ, hE, ?_⟩
  intro η hη
  apply Iso.ext
  ext M x
  apply M.unitHomEquiv.injective
  ext U
  exact (hη M x U).trans (hE M x U).symm


/-- The identity-on-sections comparison, determined uniquely by its section formula.
Source: Stacks 01FT, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def ordinarySectionsIso (A : Sheaf J CommRingCat.{max c v r}) :=
  (ordinarySectionsIso_exists.{c, v, r} J A).exists.choose

/-- The canonical K-injective computation of the recorded zeroth hypercohomology.
Source: Stacks 070I, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def sectionsResolutionIso (A : Sheaf J CommRingCat.{max c v r})
    (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective) :
    (ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A).obj
        (DerivedCategory.Q.obj I) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).obj
        (DerivedCategory.Q.obj (((homSections.{c, v, r} J A).mapHomologicalComplex
          (.up ℤ)).obj I)) :=
  letI : IsGrothendieckAbelian.{max c v r} (sequenceCoefficientModules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J A).1
  letI : I.IsKInjective := hI
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).mapIso
    ((homSections.{c, v, r} J A).rightDerivedFunctorObjQIso I)

private theorem sectionsDerives {E F : Type*} [Category* E] [Abelian E]
    [Category* F] [Abelian F] [HasDerivedCategory E] [HasDerivedCategory F]
    (T : E ⥤ F) [T.Additive] :
    (CochainComplex.KInjectives.localizerMorphism E).Derives
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (T.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private def sectionsUnit {E F : Type*} [Category* E] [Abelian E]
    [Category* F] [Abelian F] [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions E] (T : E ⥤ F) [T.Additive] :
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ T.rightDerivedFunctor where
  app I := T.rightDerivedFunctorUnitQ I
  naturality _ _ f := T.rightDerivedFunctorUnitQ_naturality f

private theorem sectionsUnit_derived {E F : Type*} [Category* E] [Abelian E]
    [Category* F] [Abelian F] [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions E] (T : E ⥤ F) [T.Additive] :
    T.rightDerivedFunctor.IsRightDerivedFunctor (sectionsUnit T)
      (HomologicalComplex.quasiIso E (.up ℤ)) := by
  apply (sectionsDerives T).isRightDerivedFunctor_of_isIso
  intro I
  have : I.obj.IsKInjective := I.property
  change IsIso (T.rightDerivedFunctorUnitQ I.obj)
  rw [T.rightDerivedFunctorUnitQ_eq]
  infer_instance

/-- The sections presentation transport on H0, fixed by its computation on resolutions.
Source: Stacks 070I, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: on each K-injective complex both derived sections presentations are computed by
ordinary sections. Apply ordinarySectionsIso termwise and conjugate by the two derived
units. Naturality on the K-injective homotopy category descends along its equivalence
with the derived category. The same equivalence proves uniqueness. No evaluation of a
varying-coefficient K-injective system is used. -/
theorem sectionsH0Comparison_exists (A : Sheaf J CommRingCat.{max c v r})
    (p : SequenceSectionsDerivedPair (sequenceCoefficientSections A)) :
    ∃! ξ : p.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
        ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A,
      ∀ (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective),
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (p.unit.app I) ≫
            ξ.hom.app (DerivedCategory.Q.obj I) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
            (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (ordinarySectionsIso.{c, v, r} J A) (.up ℤ)).hom.app I)) ≫
            (sectionsResolutionIso.{c, v, r} J A I hI).inv := by
  have : IsGrothendieckAbelian.{max c v r} (sequenceCoefficientModules A) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J A).1
  let T := homSections.{c, v, r} J A
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0
  have := p.universal
  have := sectionsUnit_derived T
  let θ := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (ordinarySectionsIso.{c, v, r} J A) (.up ℤ))
    DerivedCategory.Q
  let ζ := Functor.rightDerivedNatIso p.functor T.rightDerivedFunctor p.unit
    (sectionsUnit T) (HomologicalComplex.quasiIso (sequenceCoefficientModules A) (.up ℤ)) θ
  let ξ : p.functor ⋙ H ≅ ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A :=
    Functor.isoWhiskerRight ζ H
  have hξ (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective) :
      H.map (p.unit.app I) ≫ ξ.hom.app (DerivedCategory.Q.obj I) =
        H.map (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (ordinarySectionsIso.{c, v, r} J A) (.up ℤ)).hom.app I)) ≫
          (sectionsResolutionIso.{c, v, r} J A I hI).inv := by
    have : I.IsKInjective := hI
    have h := Functor.rightDerivedNatTrans_app p.functor T.rightDerivedFunctor
      p.unit (sectionsUnit T)
      (HomologicalComplex.quasiIso (sequenceCoefficientModules A) (.up ℤ)) θ.hom I
    have h' := congrArg H.map h
    simpa only [Functor.map_comp, ξ, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, ζ, Functor.rightDerivedNatIso_hom, sectionsUnit,
      Functor.rightDerivedFunctorUnitQ_eq, sectionsResolutionIso, Functor.mapIso_inv,
      θ, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using h'
  refine ⟨ξ, hξ, ?_⟩
  intro η hη
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  have hi := p.computes I hI
  have he : η.hom.app (DerivedCategory.Q.obj I) = ξ.hom.app (DerivedCategory.Q.obj I) := by
    apply (cancel_epi (H.map (p.unit.app I))).mp
    exact (hη I hI).trans (hξ I hI).symm
  apply (cancel_mono ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A).map e.hom)).mp
  rw [← η.hom.naturality e.hom, ← ξ.hom.naturality e.hom, he]


/-- The unique resolution-normalized transport to the hypercohomology used by 08JA.
Source: Stacks 08JA (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def sectionsH0Comparison (A : Sheaf J CommRingCat.{max c v r})
    (p : SequenceSectionsDerivedPair (sequenceCoefficientSections A)) :=
  (sectionsH0Comparison_exists.{c, v, r} J A p).exists.choose

/-- The recorded exact equivalence from sequence-site modules to strict systems, derived.
Source: Stacks 05RU, 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev toStrict : DS.{c, v, max c v r} J B τ ⥤
    DerivedCategory (StrictRingSystem (rings.{c, v, max c v r} J B τ)) :=
  letI : (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).IsEquivalence :=
    inferInstanceAs
      (strictSystemSequenceEquivalence (rings.{c, v, max c v r} J B τ)).inverse.IsEquivalence
  (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).mapDerivedCategory

/-- Identity on vertical sections specifies the comparison between the two existing
ordinary evaluations. Source: Zheng Construction 4.1; Stacks 0941
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: the ring sheaves agree on every vertical slice. Both module pushforwards
retain the original sections and maps, so identity on sections is a natural module
isomorphism. Its section formula determines every component and hence uniqueness. -/
theorem ordinaryEvaluationIso_exists (n : ℕ) :
    ∃! ξ : sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ) ⋙
        systemEvaluation (rings.{c, v, max c v r} J B τ) n ≅
          SemilinearSections.evaluation.{c, v, max c v r} J B τ n,
      ∀ (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((ξ.hom.app M).val.app U) x)
          (id : M.val.obj (op (n, U.unop)) → M.val.obj (op (n, U.unop))) := by
  let F := sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ) ⋙
    systemEvaluation (rings.{c, v, max c v r} J B τ) n
  let G := SemilinearSections.evaluation.{c, v, max c v r} J B τ n
  have he : systemSequenceVerticalRingMap (rings.{c, v, max c v r} J B τ) n =
      eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm := by
    ext U x
    simp [systemSequenceVerticalRingMap]
  let ξ : F ≅ G := SheafOfModules.pushforwardCongr he
  refine ⟨ξ, ?_, ?_⟩
  · intro M U
    rfl
  · intro η hη
    apply Iso.ext
    ext M U x
    have h := congrFun (eq_of_heq (hη M U)) x
    exact h


/-- The unique identity-on-sections evaluation comparison.
Source: Stacks 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def ordinaryEvaluationIso (n : ℕ) :=
  (ordinaryEvaluationIso_exists.{c, v, r} J B τ n).exists.choose

/-- Evaluation agrees under the actual sequence-site equivalence, using the exact-functor
localization compositor and the specified identity-on-sections comparison.
Source: Stacks 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def toStrictEvaluation (n : ℕ) :
    toStrict.{c, v, r} J B τ ⋙
        derivedSystemEvaluation (rings.{c, v, max c v r} J B τ) n ≅
      e.{c, v, max c v r} J B τ n :=
  letI : (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).IsEquivalence :=
    inferInstanceAs
      (strictSystemSequenceEquivalence (rings.{c, v, max c v r} J B τ)).inverse.IsEquivalence
  letI := SemilinearSections.evaluationAdditive.{c, v, max c v r} J B τ n
  letI := SemilinearSections.evaluationLimits.{c, v, max c v r} J B τ n
  letI := SemilinearSections.evaluationColimits.{c, v, max c v r} J B τ n
  (Functor.mapDerivedCategoryCompIso
    (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ))
    (systemEvaluation (rings.{c, v, max c v r} J B τ) n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryEvaluationIso.{c, v, r} J B τ n)

/-- The total derived direct image in the sequence-site realization, computed through
strict systems by the dependency's universal derived pair.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev limitPushforward (A : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s)) :=
  toStrict.{c, v, r} J B τ ⋙ p.functor

/-- Actual finite projection, transported by the identity-on-sections comparisons.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def projection (A : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (π : ∀ n : ℕ, p.functor ⟶ s.restriction.functor.mapDerivedCategory ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory) (n : ℕ) :
    limitPushforward.{c, v, r} J B τ A α s p ⟶
      e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)) :=
  Functor.whiskerLeft (toStrict.{c, v, r} J B τ) (π n) ≫
    Functor.whiskerLeft (toStrict.{c, v, r} J B τ)
      (sequenceRestrictionDerivedEvaluation s.restriction n).hom ≫
    Functor.whiskerRight (toStrictEvaluation.{c, v, r} J B τ n).hom
      (resD (α.app (op n)))

variable (A : Sheaf J CommRingCat.{max c v r})
  (d : Data.{c, v, r} J B τ) (a : SemilinearSections.Closed.{c, v, r} J A)
  (R : D.{c, v, max c v r} J A ⥤ DS.{c, v, max c v r} J B τ)
  (L : DS.{c, v, max c v r} J B τ ⥤ D.{c, v, max c v r} J A)
  (adj : R ⊣ L) (μ : a.tensor ⋙ R ≅ (R.prod R) ⋙ d.closed.tensor)
  (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
  (σ : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α.app (op n)))
  (ρ : ∀ n : ℕ, R ⋙ e.{c, v, max c v r} J B τ n ≅ (σ n).T)

/-- Evaluation of the actual system tensor-pullback comparison, transported along rho.
Its representative model in the theorem below fixes this very map, before choosing nu.
Source: Stacks 07A4, its total-complex comparison on flat-term K-flat representatives
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def evaluatedTensorComparison (n : ℕ) :
    a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor :=
  Functor.isoWhiskerLeft a.tensor (ρ n).symm ≪≫
    Functor.isoWhiskerRight μ (e.{c, v, max c v r} J B τ n) ≪≫
    Functor.isoWhiskerLeft (R.prod R) (d.tensorEvaluation n) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (ρ n) (ρ n)) (d.levelClosed n).tensor

/-- V is the recorded derived internal Hom over A.
Source: Stacks 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev sourceHom (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  (internalHom.{c, v, r} J A).obj (op P, L.obj N)

/-- J is the recorded derived internal Hom on the ringed sequence site.
Source: Stacks 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev systemHom (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  (internalHom.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)).obj (op (R.obj P), N)

/-- The finite internal Hom, with scalar extension only in its first input.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev levelHom (P : D.{c, v, max c v r} J A)
    (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (internalHom.{c, v, r} J (B n)).obj
    (op ((σ n).T.obj P), (e.{c, v, max c v r} J B τ n).obj N)

/-- The evaluation-defined b, with no arbitrary comparison map.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def comparison (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  ClosedAdjunctionComparison.comparison a.tensor d.closed.tensor
    (internalHom.{c, v, r} J A)
    (internalHom.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    a.transpose d.closed.transpose R L (fun X Y ↦ (μ.app (X, Y)).symm) adj P N

/-- Delta is the unit followed by L(b), as in the closed-adjunction dependency.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def delta (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  ClosedAdjunctionComparison.adjointComparison a.tensor d.closed.tensor
    (internalHom.{c, v, r} J A)
    (internalHom.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    a.transpose d.closed.transpose R L (fun X Y ↦ (μ.app (X, Y)).symm) adj P N

/-- The cartesian first-input Hom comparison followed by the scalar-extension identification.
Source: Stacks 08J9; Zheng Construction 4.1
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def homIdentification (P : D.{c, v, max c v r} J A)
    (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :
    (e.{c, v, max c v r} J B τ n).obj (systemHom.{c, v, r} J B τ A R P N) ≅
      levelHom.{c, v, r} J B τ A α σ P N n :=
  (d.homEvaluation (R.obj P) hP n).app N ≪≫
    (internalHom.{c, v, r} J (B n)).mapIso
      (Iso.prod ((ρ n).app P).symm.op (Iso.refl _))

/-- Component of the system counit, with its source identified with scalar extension.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def counitLevel (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :
    (σ n).T.obj (L.obj N) ⟶ (e.{c, v, max c v r} J B τ n).obj N :=
  (ρ n).inv.app (L.obj N) ≫
    (e.{c, v, max c v r} J B τ n).map (adj.counit.app N)

/-- Reduced evaluation followed by the actual counit component. The inverse tensor
comparison is precisely the displayed canonical tensor reassociation in the node.
Source: Stacks 07A4, 07A6, 08J9
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def reducedEvaluation
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (ν n).inv.app (sourceHom.{c, v, r} J B τ A L P N, P) ≫
    (σ n).T.map (a.evaluation P (L.obj N)) ≫
      counitLevel.{c, v, r} J B τ A R L adj α σ ρ N n

/-- The scalar internal-Hom adjunction after H_A(P,pi_n), using its existing five
normalized scalar and closed Hom bijections. This is the internal scalar-extension map,
not an integral Hom/tensor base-change isomorphism.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def internalScalarMap
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (internalHom.{c, v, r} J A).map (Prod.mkHom (𝟙 (op P)) ((π n).app N)) ≫
    (ClosedScalarHom.component a (d.levelClosed n) (σ n).adjunction (ν n) P
      ((e.{c, v, max c v r} J B τ n).obj N)).inv

/-- Finite projection of delta, with the specified cartesian-Hom identification.
Source: Stacks 07A6, 08J9, 0941
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def finiteProjection
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :=
  delta.{c, v, r} J B τ A d a R L adj μ P N ≫
    (π n).app (systemHom.{c, v, r} J B τ A R P N) ≫
    (resD (α.app (op n))).map
      (homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n).hom

/-- The finite scalar-extension adjunct of a projected morphism, then its closed transpose.
Source: Stacks 07A6 and 08J9
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def uncurried
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ)
    (q : sourceHom.{c, v, r} J B τ A L P N ⟶
      (resD (α.app (op n))).obj (levelHom.{c, v, r} J B τ A α σ P N n)) :=
  ((d.levelClosed n).transpose _ ((σ n).T.obj P)
    ((e.{c, v, max c v r} J B τ n).obj N)).symm
      (((σ n).adjunction.homEquiv _ _).symm q)

/-- The global map RΓ(delta), transported to the total limit and projected at n,
then identified with finite derived sections of the evaluated internal Hom.
Source: Stacks 0D6E, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def globalProjection
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (hL : L ≅ limitPushforward.{c, v, r} J B τ A α s p)
    (rl : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ⥤ AddCommGrpCat.{max c v r}))
    (πL : ∀ n : ℕ, rl.functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
        (op n)).mapDerivedCategory)
    (κ : p.functor ⋙ (s.finite A).functor ≅ s.global ⋙ rl.functor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :=
  (s.finite A).functor.map (delta.{c, v, r} J B τ A d a R L adj μ P N) ≫
    (s.finite A).functor.map (hL.hom.app (systemHom.{c, v, r} J B τ A R P N)) ≫
    κ.hom.app ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N)) ≫
    (πL n).app (s.global.obj ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N))) ≫
    (s.finiteEvaluation n).hom.app ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N)) ≫
    (s.finite (B n)).functor.map
      ((toStrictEvaluation.{c, v, r} J B τ n).hom.app
        (systemHom.{c, v, r} J B τ A R P N) ≫
        (homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n).hom)

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

attribute [local irreducible] ordinarySectionsIso sectionsH0Comparison
  toStrictEvaluation homIdentification
  CategoryTheory.Functor.rightDerivedFunctorObjQIso
  CategoryTheory.Functor.rightDerivedFunctorUnitQ

private theorem sectionsComparison_inv {E F : Type*} [Category* E] [Abelian E]
    [Category* F] [Abelian F] [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions E] (T : E ⥤ F) [T.Additive]
    (I : CochainComplex E ℤ) [I.IsKInjective] :
    (T.rightDerivedFunctorObjQIso I).inv = coefficientRightDerivedComparison T I := by
  rw [← T.rightDerivedFunctorUnitQ_eq]
  unfold CategoryTheory.Functor.rightDerivedFunctorUnitQ coefficientRightDerivedComparison
  rfl

private theorem sectionsH0Comparison_unit (A : Sheaf J CommRingCat.{max c v r})
    (p : SequenceSectionsDerivedPair (sequenceCoefficientSections A))
    (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (p.unit.app I) ≫
        (sectionsH0Comparison.{c, v, r} J A p).hom.app (DerivedCategory.Q.obj I) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
        (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (ordinarySectionsIso.{c, v, r} J A) (.up ℤ)).hom.app I) ≫
          coefficientSiteSectionsComparison.{r, c, v} J A I) := by
  have : IsGrothendieckAbelian.{max c v r} (sequenceCoefficientModules A) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J A).1
  have : I.IsKInjective := hI
  have h := (sectionsH0Comparison_exists.{c, v, r} J A p).exists.choose_spec I hI
  have he : (sectionsResolutionIso.{c, v, r} J A I hI).inv =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
        (coefficientSiteSectionsComparison.{r, c, v} J A I) := by
    exact congrArg ((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map)
      (sectionsComparison_inv (homSections.{c, v, r} J A) I)
  unfold sectionsH0Comparison
  rw [Functor.map_comp, ← he]
  exact h

private theorem sections_projection_comp
    {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    (F : X ⥤ Z) (G : Y ⥤ Z) (U : Y ⥤ X) (c : U ⋙ F ⟶ G)
    {V W P : X} {E E' : Y} {Q : Z}
    (δ : V ⟶ W) (l : W ⟶ P) (t : P ⟶ U.obj E)
    (k : F.obj P ⟶ Q) (p : Q ⟶ G.obj E)
    (h : k ≫ p = F.map t ≫ c.app E) (j : E ⟶ E') :
    F.map δ ≫ F.map l ≫ k ≫ p ≫ G.map j =
      F.map (δ ≫ l ≫ t ≫ U.map j) ≫ c.app E' := by
  have hn := c.naturality j
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc k p, h]
  simp only [Category.assoc, Functor.map_comp]
  erw [← hn]

private theorem projection_transpose
    {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    {F : X ⥤ Y} {G : Y ⥤ X} (ad : F ⊣ G)
    (E : Y ⥤ Z) {T : X ⥤ Z} {U : Z ⥤ X} (sa : T ⊣ U)
    (ρ : F ⋙ E ≅ T) (π : G ⟶ E ⋙ U)
    (hu : ∀ M : X, ad.unit.app M ≫ π.app (F.obj M) ≫
      U.map (ρ.hom.app M) = sa.unit.app M)
    {M : X} {N : Y} {Q : Z} (f : F.obj M ⟶ N) (t : E.obj N ⟶ Q) :
    (ad.homEquiv M N f) ≫ π.app N ≫ U.map t =
      sa.homEquiv M Q (ρ.inv.app M ≫ E.map f ≫ t) := by
  erw [ad.homEquiv_unit, sa.homEquiv_unit]
  have hn := π.naturality f
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← Category.assoc (G.map f), hn]
  have hunit : ad.unit.app M ≫ π.app (F.obj M) =
      sa.unit.app M ≫ U.map (ρ.inv.app M) := by
    apply (cancel_mono (U.map (ρ.hom.app M))).mp
    erw [Category.assoc, hu]
    simp only [Category.assoc, ← U.map_comp, Iso.inv_hom_id_app]
    erw [U.map_id, Category.comp_id]
  simp only [← Category.assoc]
  erw [hunit]
  simp only [Category.assoc, Functor.map_comp]

private theorem closed_uncurry {X : Type*} [Category* X] {H : Xᵒᵖ × X ⥤ X}
    (S : CoefficientClosedStructure H) {T P Q : X} (f : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.evaluation P Q := by
  change (@MonoidalCategory.tensorRight X _ S.monoidal P).map f ≫
    S.evaluation P Q = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem closed_evaluation_target {X : Type*} [Category* X]
    {H : Xᵒᵖ × X ⥤ X} (S : CoefficientClosedStructure H)
    (P Q Q' : X) (f : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P)) f)) (𝟙 P)) ≫
      S.evaluation P Q' = S.evaluation P Q ≫ f := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction P).counit.naturality f

private theorem closed_evaluation_source {X : Type*} [Category* X]
    {H : Xᵒᵖ × X ⥤ X} (S : CoefficientClosedStructure H)
    (P P' Q : X) (f : P' ⟶ P) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) f) ≫ S.evaluation P Q := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using S.evaluation_naturality P P' Q f

private theorem closed_uncurry_evaluation
    {X Y : Type*} [Category* X] [Category* Y]
    {H : Xᵒᵖ × X ⥤ X} {I : Yᵒᵖ × Y ⥤ Y}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    (E : X ⥤ Y) (χ : S.tensor ⋙ E ≅ (E.prod E) ⋙ T.tensor)
    {V P N : X} {V' P' : Y} (b : V ⟶ H.obj (op P, N))
    (h : E.obj (H.obj (op P, N)) ⟶ I.obj (op (E.obj P), E.obj N))
    (he : T.tensor.map (Prod.mkHom h (𝟙 (E.obj P))) ≫
      T.evaluation (E.obj P) (E.obj N) =
        χ.inv.app (H.obj (op P, N), P) ≫ E.map (S.evaluation P N))
    (i : V' ⟶ E.obj V) (k : P' ⟶ E.obj P) :
    (T.transpose V' P' (E.obj N)).symm
        (i ≫ E.map b ≫ h ≫ I.map (Prod.mkHom k.op (𝟙 (E.obj N)))) =
      T.tensor.map (Prod.mkHom i k) ≫ χ.inv.app (V, P) ≫
        E.map ((S.transpose V P N).symm b) := by
  erw [closed_uncurry, closed_uncurry]
  have hs := closed_evaluation_source T (E.obj P) P' (E.obj N) k
  calc
    _ = T.tensor.map (Prod.mkHom (i ≫ E.map b ≫ h) (𝟙 P')) ≫
        (T.tensor.map (Prod.mkHom (I.map (Prod.mkHom k.op (𝟙 (E.obj N))))
          (𝟙 P')) ≫ T.evaluation P' (E.obj N)) := by
            simp only [← Category.assoc, ← T.tensor.map_comp]
            congr 2
            simp
    _ = T.tensor.map (Prod.mkHom (i ≫ E.map b ≫ h) (𝟙 P')) ≫
        T.tensor.map (Prod.mkHom (𝟙 _) k) ≫ T.evaluation (E.obj P) (E.obj N) := by
          erw [hs]
    _ = T.tensor.map (Prod.mkHom i k) ≫
        T.tensor.map (Prod.mkHom (E.map b) (𝟙 (E.obj P))) ≫
        (T.tensor.map (Prod.mkHom h (𝟙 (E.obj P))) ≫
          T.evaluation (E.obj P) (E.obj N)) := by
            simp only [← Category.assoc, ← T.tensor.map_comp]
            congr 2
            simp
    _ = T.tensor.map (Prod.mkHom i k) ≫ χ.inv.app (V, P) ≫
        E.map (S.tensor.map (Prod.mkHom b (𝟙 P)) ≫ S.evaluation P N) := by
      erw [he]
      have hn := χ.inv.naturality (Prod.mkHom b (𝟙 P))
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      simp only [CategoryTheory.Functor.map_id] at hn
      simpa only [Category.assoc, Functor.map_comp] using
        congrArg (fun z ↦ T.tensor.map (Prod.mkHom i k) ≫ z ≫
          E.map (S.evaluation P N)) hn

private theorem closed_scalar_uncurry
    {X Y : Type*} [Category* X] [Category* Y]
    {H : Xᵒᵖ × X ⥤ X} {I : Yᵒᵖ × Y ⥤ Y}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : X ⥤ Y} {U : Y ⥤ X} (ad : F ⊣ U)
    (χ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
    (P Q : X) (N : Y) (k : Q ⟶ U.obj N) :
    (T.transpose _ (F.obj P) N).symm
        ((ad.homEquiv _ _).symm
          (H.map (Prod.mkHom (𝟙 (op P)) k) ≫
            (ClosedScalarHom.component S T ad χ P N).inv)) =
      χ.inv.app (H.obj (op P, Q), P) ≫ F.map (S.evaluation P Q) ≫
        (ad.homEquiv Q N).symm k := by
  let b := H.map (Prod.mkHom (𝟙 (op P)) k) ≫
    (ClosedScalarHom.component S T ad χ P N).inv
  have hb := ClosedScalarHom.component_rep S T ad χ (H.obj (op P, Q)) P N b
  dsimp only [b] at hb
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hb
  have hc := congrArg (S.transpose _ P (U.obj N)).symm hb
  dsimp only [ClosedScalarHom.bijection, Equiv.trans_apply, Iso.homCongr,
    Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom] at hc
  erw [Equiv.symm_apply_apply, Category.comp_id] at hc
  erw [closed_uncurry S, closed_evaluation_target S] at hc
  have hd := congrArg (ad.homEquiv _ N).symm hc
  erw [Equiv.symm_apply_apply, ad.homEquiv_naturality_left_symm] at hd
  apply (cancel_epi (χ.hom.app (H.obj (op P, Q), P))).mp
  change χ.hom.app (H.obj (op P, Q), P) ≫ _ = _ at hd
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ad.homEquiv_naturality_left_symm] using hd

private theorem projection_counit
    {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    {F : X ⥤ Y} {G : Y ⥤ X} (ad : F ⊣ G)
    (E : Y ⥤ Z) {T : X ⥤ Z} {U : Z ⥤ X} (sa : T ⊣ U)
    (ρ : F ⋙ E ≅ T) (π : G ⟶ E ⋙ U)
    (hu : ∀ M : X, ad.unit.app M ≫ π.app (F.obj M) ≫
      U.map (ρ.hom.app M) = sa.unit.app M) (N : Y) :
    (sa.homEquiv _ _).symm (π.app N) =
      ρ.inv.app (G.obj N) ≫ E.map (ad.counit.app N) := by
  have h := projection_transpose ad E sa ρ π hu (ad.counit.app N) (𝟙 _)
  have hc : ad.homEquiv (G.obj N) N (ad.counit.app N) = 𝟙 _ := by
    erw [← ad.homEquiv_symm_id, Equiv.apply_symm_apply]
  change ad.homEquiv (G.obj N) N (ad.counit.app N) ≫ π.app N ≫ U.map (𝟙 _) =
    sa.homEquiv _ _ (ρ.inv.app (G.obj N) ≫ E.map (ad.counit.app N) ≫ 𝟙 _) at h
  erw [hc, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.comp_id] at h
  exact (sa.homEquiv _ _).symm_apply_eq.mpr h

omit [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify J AddCommGrpCat.{max c v r}] in
private theorem finite_uncurry
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (hu : ∀ (X : D.{c, v, max c v r} J A) (n : ℕ),
      adj.unit.app X ≫ (π n).app (R.obj X) ≫
        (resD (α.app (op n))).map ((ρ n).hom.app X) = (σ n).adjunction.unit.app X)
    (hm : ∀ (X Y : D.{c, v, max c v r} J A) (n : ℕ),
      (e.{c, v, max c v r} J B τ n).map (μ.hom.app (X, Y)) ≫
          (d.tensorEvaluation n).hom.app (R.obj X, R.obj Y) ≫
          (d.levelClosed n).tensor.map (Prod.mkHom ((ρ n).hom.app X) ((ρ n).hom.app Y)) =
        (ρ n).hom.app (a.tensor.obj (X, Y)) ≫ (ν n).hom.app (X, Y))
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :
    uncurried.{c, v, r} J B τ A d L α σ P N n
        (finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n) =
      reducedEvaluation.{c, v, r} J B τ A d a R L adj α σ ρ ν P N n := by
  let V := sourceHom.{c, v, r} J B τ A L P N
  let M := systemHom.{c, v, r} J B τ A R P N
  let E := e.{c, v, max c v r} J B τ n
  let T := (σ n).T
  let S := d.levelClosed n
  let b := comparison.{c, v, r} J B τ A d a R L adj μ P N
  let h := (d.homEvaluation (R.obj P) hP n).hom.app N
  let i := homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n
  have hq : finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n =
      (σ n).adjunction.homEquiv _ _ ((ρ n).inv.app V ≫ E.map b ≫ i.hom) := by
    change adj.homEquiv _ _ b ≫ (π n).app _ ≫ (resD (α.app (op n))).map i.hom = _
    exact projection_transpose adj E (σ n).adjunction (ρ n) (π n)
        (fun X ↦ hu X n) b i.hom
  dsimp only [uncurried]
  erw [hq, Equiv.symm_apply_apply]
  have hb : (d.closed.transpose _ (R.obj P) N).symm b =
      μ.inv.app (V, P) ≫ R.map (a.evaluation P (L.obj N)) ≫ adj.counit.app N := by
    dsimp only [b, comparison, ClosedAdjunctionComparison.comparison]
    erw [Equiv.symm_apply_apply]
    simp only [ClosedAdjunctionComparison.evaluation, CoefficientClosedStructure.transpose]
    erw [(a.adjunction P).homEquiv_symm_id]
    rfl
  have hh := closed_uncurry_evaluation d.closed S E (d.tensorEvaluation n) b h
    (d.homEvaluation_evaluation (R.obj P) N hP n)
    ((ρ n).inv.app V) ((ρ n).inv.app P)
  change (S.transpose _ (T.obj P) (E.obj N)).symm
    ((ρ n).inv.app V ≫ E.map b ≫ i.hom) = _
  have hi : i.hom = h ≫ (internalHom.{c, v, r} J (B n)).map
      (Prod.mkHom ((ρ n).inv.app P).op (𝟙 (E.obj N))) := by
    unfold i homIdentification
    rfl
  erw [hi]
  erw [hh, hb]
  have ht : S.tensor.map (Prod.mkHom ((ρ n).inv.app V) ((ρ n).inv.app P)) ≫
      (d.tensorEvaluation n).inv.app (R.obj V, R.obj P) ≫ E.map (μ.inv.app (V, P)) =
        (ν n).inv.app (V, P) ≫ (ρ n).inv.app (a.tensor.obj (V, P)) := by
    have hm' := hm V P n
    change E.map (μ.hom.app (V, P)) ≫
      (d.tensorEvaluation n).hom.app (R.obj V, R.obj P) ≫
        S.tensor.map (Prod.mkHom ((ρ n).hom.app V) ((ρ n).hom.app P)) =
      (ρ n).hom.app (a.tensor.obj (V, P)) ≫ (ν n).hom.app (V, P) at hm'
    have heq : E.mapIso (μ.app (V, P)) ≪≫
        (d.tensorEvaluation n).app (R.obj V, R.obj P) ≪≫
          S.tensor.mapIso (Iso.prod ((ρ n).app V) ((ρ n).app P)) =
        (ρ n).app (a.tensor.obj (V, P)) ≪≫ (ν n).app (V, P) := by
      apply Iso.ext
      exact hm'
    have heq' := congrArg Iso.inv heq
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv,
      Iso.app_inv, Category.assoc] using heq'
  change S.tensor.map (Prod.mkHom ((ρ n).inv.app V) ((ρ n).inv.app P)) ≫
      (d.tensorEvaluation n).inv.app (R.obj V, R.obj P) ≫
        E.map (μ.inv.app (V, P) ≫ R.map (a.evaluation P (L.obj N)) ≫
          adj.counit.app N) = _
  erw [Functor.map_comp, Functor.map_comp]
  simp only [← Category.assoc]
  erw [← Category.assoc] at ht
  erw [ht]
  have hn := (ρ n).inv.naturality (a.evaluation P (L.obj N))
  change T.map (a.evaluation P (L.obj N)) ≫ (ρ n).inv.app (L.obj N) =
    (ρ n).inv.app (a.tensor.obj (V, P)) ≫ E.map (R.map (a.evaluation P (L.obj N))) at hn
  dsimp only [reducedEvaluation, counitLevel]
  simp only [Category.assoc]
  erw [← Category.assoc ((ρ n).inv.app _), ← hn]
  simp only [Category.assoc]
  rfl

/-- The finite projection of the evaluation-defined enriched adjunction is uniquely
characterized by reduced evaluation, equals the internal scalar-extension adjunction
following H_A(P,pi_n), and has the same description after the specified strict-system
sections/limit comparison. Its degree-zero Hom action is h sent to e_n after scalar
extension of h.

The derived pair p, its complex-normalized projections piP, and hL present the actual
right derived sequence projection. The unit equation normalizes the transported
adjunction and rho. The representative model for evaluatedTensorComparison fixes
actual evaluations of mu by the ordinary pure-tensor formula, the total summand maps,
and the K-flat localization square; the tensor equation then fixes nu to these maps.
These are presentations of the specified operations, not flatness,
perfectness, boundedness, or a normalization assumption on the Hom system.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6E;
agent uncurrying of the enriched finite projection, returned calculus step 14
(blueprint: lem-coef-enriched-sequence-projection-formula).

Proof plan, following the node's six steps:
1. Naturality of the actual total-limit projection at b and the unit normalization give
   pi_n(delta) = Res(b_n) eta_n, by lem-coef-sequence-pushforward-limit-projections and
   lem-coef-sequence-projection-derived-adjunction. This is an equality of derived maps.
2. Uncurry b using lem-coef-closed-adjunction-enriched-isomorphism. Apply the tensor
   evaluation and cartesian first-input Hom evaluation of lem-coef-semilinear-derived-sections.
   The tensor-pullback comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback
   is fixed after evaluation by hMuModel: its ordinary pure tensors and total summands
   give the canonical 07A4 comparison on K-flat representatives. The compatibility
   equation identifies this actual evaluated comparison with nu. Thus the resulting
   map is precisely reducedEvaluation; no faithfulness of evaluation is used.
3. Scalar transposition (lem-pur-sheaf-ring-derived-coefficient-adjunction), followed by
   closed transposition (lem-sf-ringed-derived-closed-symmetric-monoidal), is a bijection.
   Step 1 therefore identifies the finite projection as the unique map with this uncurry.
4. Uncurry the inverse scalar internal-Hom comparison of lem-sfb-dc-hom-scalar-adjunction
   after H_A(P,pi_n). Naturality of evaluation and the counit normalization give the same
   reduced evaluation. Step 3 proves the equivalent internal formula without extending
   the second Hom input.
5. Use lem-coef-sequence-sections-limit-comparison for the strict right derived pair p.
   Its normalized composition comparison and finite comparisons are natural. Its nth
   projection is sections of piP followed by inverse scalar restriction comparison.
   Transport through toStrictEvaluation and hL, then apply sections to step 4. This is
   the asserted global mapping-complex formula on arbitrary Hom systems.
6. Take degree zero using coefficientHomZeroEquiv of def-coef-hom-zero-cycle-class,
   uniquely fixed by naturality and its representative normalization: a degree-zero Hom
   cocycle for a chain map g represents Q(g), with the inverse resolution augmentation.
   Naturality makes H_A(P,pi_n) postcomposition with pi_n. The normalized scalar adjunction
   sends that composite to scalar(h) followed by the evaluated system counit, giving the
   final displayed Hom equation for H0 of globalProjection itself. The uniquely
   resolution-normalized sectionsH0Comparison transports the limit-based sections to
   the hypercohomology used by 08JA at both endpoints. No evaluated K-injective system
   is assumed K-injective. -/
theorem enrichedSequenceProjectionFormula
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (_hs : s.Normalized)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (πP : ∀ n : ℕ, p.functor ⟶ s.restriction.functor.mapDerivedCategory ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory)
    (_hπP : ∀ (X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ)
      (n : ℕ),
      p.unit.app X ≫ (πP n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategory.map
            (s.restriction.functor.mapDerivedCategoryFactors.hom.app X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategoryFactors.hom.app
            ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)))
    (hL : L ≅ limitPushforward.{c, v, r} J B τ A α s p)
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (_hπ : ∀ n : ℕ, π n = hL.hom ≫ projection.{c, v, r} J B τ A α s p πP n)
    (_hunit : ∀ (X : D.{c, v, max c v r} J A) (n : ℕ),
      adj.unit.app X ≫ (π n).app (R.obj X) ≫
        (resD (α.app (op n))).map ((ρ n).hom.app X) = (σ n).adjunction.unit.app X)
    (aModels : Models.{c, v, r} J A a)
    (_hμModel : ∀ n : ℕ, ScalarTensorComparisonModel.{c, v, r} J A (B n)
      (α.app (op n)) (σ n) a (d.levelClosed n) aModels (d.levelTensorModels n)
      (evaluatedTensorComparison.{c, v, r} J B τ A d a R μ α σ ρ n))
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (_hμ : ∀ (X Y : D.{c, v, max c v r} J A) (n : ℕ),
      (e.{c, v, max c v r} J B τ n).map (μ.hom.app (X, Y)) ≫
          (d.tensorEvaluation n).hom.app (R.obj X, R.obj Y) ≫
          (d.levelClosed n).tensor.map (Prod.mkHom ((ρ n).hom.app X) ((ρ n).hom.app Y)) =
        (ρ n).hom.app (a.tensor.obj (X, Y)) ≫ (ν n).hom.app (X, Y)) :
    ∃ (rl : SequenceSectionsDerivedPair
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ⥤ AddCommGrpCat.{max c v r}))
      (πL : ∀ n : ℕ, rl.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
          (op n)).mapDerivedCategory)
      (κ : p.functor ⋙ (s.finite A).functor ≅ s.global ⋙ rl.functor),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ℤ) (n : ℕ),
        rl.unit.app X ≫ (πL n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
            (op n)).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ∧
      (∀ X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ,
        (s.finite A).unit.app
            (((sequenceProjectionDirectImage s).mapHomologicalComplex (.up ℤ)).obj X) ≫
          (s.finite A).functor.map (p.unit.app X) ≫ κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (sequenceSectionsLimitOrdinary s) (.up ℤ)).hom.app X) ≫
          rl.unit.app (((s.restriction.functor ⋙ sequenceTowerSections A).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          rl.functor.map (s.tower.unit.app
            ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
          rl.functor.map (s.tower.functor.map
            (s.restriction.functor.mapDerivedCategoryFactors.inv.app X))) ∧
      ∀ (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
        (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P))
        (_hN : Normalized.{c, v, max c v r} J B τ d.scalar N) (n : ℕ),
        (uncurried.{c, v, r} J B τ A d L α σ P N n
            (finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n) =
          reducedEvaluation.{c, v, r} J B τ A d a R L adj α σ ρ ν P N n) ∧
        (∀ q : sourceHom.{c, v, r} J B τ A L P N ⟶
            (resD (α.app (op n))).obj (levelHom.{c, v, r} J B τ A α σ P N n),
          uncurried.{c, v, r} J B τ A d L α σ P N n q =
              reducedEvaluation.{c, v, r} J B τ A d a R L adj α σ ρ ν P N n →
            q = finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n) ∧
        (finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n =
          internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n) ∧
        (globalProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ s p hL rl πL κ P N hP n =
          (s.finite A).functor.map
              (internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n) ≫
            (s.scalar (α.app (op n))).inv.app (levelHom.{c, v, r} J B τ A α σ P N n)) ∧
        (∀ h : P ⟶ L.obj N,
          coefficientHomZeroEquiv.{r, c, v} J (B n)
            ((σ n).T.obj P) ((e.{c, v, max c v r} J B τ n).obj N)
            (((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
                (globalProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ
                  s p hL rl πL κ P N hP n) ≫
              (sectionsH0Comparison.{c, v, r} J (B n) (s.finite (B n))).hom.app
                (levelHom.{c, v, r} J B τ A α σ P N n))
              ((sectionsH0Comparison.{c, v, r} J A (s.finite A)).inv.app
                (sourceHom.{c, v, r} J B τ A L P N)
                ((coefficientHomZeroEquiv.{r, c, v} J A P (L.obj N)).symm h))) =
            (σ n).T.map h ≫ counitLevel.{c, v, r} J B τ A R L adj α σ ρ N n) := by
  obtain ⟨p₀, rl, π₀, πL, κ₀, hp₀, hπL, hκ₀, hfinite₀⟩ :=
    coefficientSequenceSectionsLimitComparison (rings.{c, v, max c v r} J B τ) A α s _hs
  have := p.universal
  have := p₀.universal
  let W := HomologicalComplex.quasiIso
    (StrictRingSystem (rings.{c, v, max c v r} J B τ)) (.up ℤ)
  let ε := Functor.rightDerivedUnique p.functor p₀.functor p.unit p₀.unit W
  have hε (X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ) :
      p.unit.app X ≫ ε.hom.app (DerivedCategory.Q.obj X) = p₀.unit.app X := by
    simpa only [ε, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app p.functor p₀.functor p.unit p₀.unit W (𝟙 _) X
  have hπ (n : ℕ) : ε.hom ≫ π₀ n = πP n := by
    apply Functor.rightDerived_ext p.functor p.unit W
    apply NatTrans.ext
    funext X
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← Category.assoc, hε]
    apply (cancel_mono
      (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory.map
          (s.restriction.functor.mapDerivedCategoryFactors.hom.app X) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app
            ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X))).mp
    simpa only [Category.assoc] using (hp₀ X n).trans (_hπP X n).symm
  let κ := Functor.isoWhiskerRight ε (s.finite A).functor ≪≫ κ₀
  have hκ (X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ) :
      (s.finite A).unit.app
          (((sequenceProjectionDirectImage s).mapHomologicalComplex (.up ℤ)).obj X) ≫
        (s.finite A).functor.map (p.unit.app X) ≫ κ.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (sequenceSectionsLimitOrdinary s) (.up ℤ)).hom.app X) ≫
        rl.unit.app (((s.restriction.functor ⋙ sequenceTowerSections A).mapHomologicalComplex
          (.up ℤ)).obj X) ≫
        rl.functor.map (s.tower.unit.app
          ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        rl.functor.map (s.tower.functor.map
          (s.restriction.functor.mapDerivedCategoryFactors.inv.app X)) := by
    dsimp only [κ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app]
    rw [← Category.assoc ((s.finite A).functor.map _), ← Functor.map_comp, hε]
    exact hκ₀ X
  have hfinite (M : DerivedCategory (StrictRingSystem (rings.{c, v, max c v r} J B τ)))
      (n : ℕ) :
      κ.hom.app M ≫ (πL n).app (s.global.obj M) ≫ (s.finiteEvaluation n).hom.app M =
        (s.finite A).functor.map ((πP n).app M) ≫
          (s.finite A).functor.map
            ((sequenceRestrictionDerivedEvaluation s.restriction n).hom.app M) ≫
          (s.scalar (α.app (op n))).inv.app
            ((derivedSystemEvaluation (rings.{c, v, max c v r} J B τ) n).obj M) := by
    have hh := congrArg (fun f ↦ (s.finite A).functor.map (ε.hom.app M) ≫ f)
      (hfinite₀ M n)
    have hp := congrArg (fun t ↦ t.app M) (hπ n)
    dsimp only [NatTrans.comp_app] at hp
    rw [← (s.finite A).functor.map_comp_assoc, hp] at hh
    simpa only [κ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.assoc] using hh
  refine ⟨rl, πL, κ, hπL, hκ, ?_⟩
  intro P N hP hN n
  have hu := finite_uncurry.{c, v, r} J B τ A d a R L adj μ α σ ρ π ν _hunit _hμ P N hP n
  have his : finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n =
      internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n := by
    apply ((σ n).adjunction.homEquiv _ _).symm.injective
    apply ((d.levelClosed n).transpose _ _ _).symm.injective
    change uncurried.{c, v, r} J B τ A d L α σ P N n _ = _
    rw [hu]
    symm
    change ((d.levelClosed n).transpose _ _ _).symm
      (((σ n).adjunction.homEquiv _ _).symm
        (internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n)) = _
    rw [internalScalarMap, closed_scalar_uncurry]
    rw [projection_counit adj (e.{c, v, max c v r} J B τ n) (σ n).adjunction (ρ n) (π n)
      (fun X ↦ _hunit X n) N]
    rfl
  have hg : globalProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ s p hL rl πL κ P N hP n =
      (s.finite A).functor.map (internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n) ≫
        (s.scalar (α.app (op n))).inv.app (levelHom.{c, v, r} J B τ A α σ P N n) := by
    let M := systemHom.{c, v, r} J B τ A R P N
    let f := (toStrictEvaluation.{c, v, r} J B τ n).hom.app M ≫
      (homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n).hom
    have hc := congrArg (fun t ↦ t.app M) (_hπ n)
    dsimp only [NatTrans.comp_app, projection, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hc
    have hh := sections_projection_comp (s.finite A).functor (s.finite (B n)).functor
      (resD (α.app (op n))) (s.scalar (α.app (op n))).inv
      (delta.{c, v, r} J B τ A d a R L adj μ P N) (hL.hom.app M)
      ((πP n).app ((toStrict.{c, v, r} J B τ).obj M) ≫
        (sequenceRestrictionDerivedEvaluation s.restriction n).hom.app
          ((toStrict.{c, v, r} J B τ).obj M))
      (κ.hom.app ((toStrict.{c, v, r} J B τ).obj M))
      ((πL n).app (s.global.obj ((toStrict.{c, v, r} J B τ).obj M)) ≫
        (s.finiteEvaluation n).hom.app ((toStrict.{c, v, r} J B τ).obj M))
      (by simpa only [Functor.map_comp, Category.assoc] using
        hfinite ((toStrict.{c, v, r} J B τ).obj M) n) f
    have hq : delta.{c, v, r} J B τ A d a R L adj μ P N ≫ hL.hom.app M ≫
        ((πP n).app ((toStrict.{c, v, r} J B τ).obj M) ≫
          (sequenceRestrictionDerivedEvaluation s.restriction n).hom.app
            ((toStrict.{c, v, r} J B τ).obj M)) ≫
        (resD (α.app (op n))).map f =
      finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n := by
      dsimp only [finiteProjection, f]
      rw [hc]
      simp only [Functor.map_comp, Category.assoc]
    rw [hq, his] at hh
    simpa only [globalProjection, Category.assoc] using hh
  refine ⟨hu, ?_, his, hg, ?_⟩
  · intro q hq
    apply ((σ n).adjunction.homEquiv _ _).symm.injective
    apply ((d.levelClosed n).transpose _ _ _).symm.injective
    exact hq.trans hu.symm
  · intro h
    rw [hg]
    have hν (n : ℕ) : evaluatedTensorComparison.{c, v, r} J B τ A d a R μ α σ ρ n = ν n := by
      apply Iso.ext
      ext X
      rcases X with ⟨X, Y⟩
      have hm := _hμ X Y n
      apply (cancel_epi ((ρ n).hom.app (a.tensor.obj (X, Y)))).mp
      simpa only [evaluatedTensorComparison, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        NatIso.prod_hom, NatTrans.prod, Functor.prod_map, Functor.prod_obj,
        Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc] using hm
    have hm : ScalarTensorComparisonModel.{c, v, r} J A (B n) (α.app (op n))
        (σ n) a (d.levelClosed n) aModels (d.levelTensorModels n) (ν n) := by
      rw [← hν n]
      exact _hμModel n
    have hoA : ∀ (M : sequenceCoefficientModules A)
        (x : (sequenceCoefficientSections A).obj M) (U : Cᵒᵖ),
        (M.unitHomEquiv ((ordinarySectionsIso.{c, v, r} J A).hom.app M x)).val U =
          (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x := by
      unfold ordinarySectionsIso
      exact (ordinarySectionsIso_exists.{c, v, r} J A).exists.choose_spec
    have hoB : ∀ (M : sequenceCoefficientModules (B n))
        (x : (sequenceCoefficientSections (B n)).obj M) (U : Cᵒᵖ),
        (M.unitHomEquiv ((ordinarySectionsIso.{c, v, r} J (B n)).hom.app M x)).val U =
          (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J (B n)) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x := by
      unfold ordinarySectionsIso
      exact (ordinarySectionsIso_exists.{c, v, r} J (B n)).exists.choose_spec
    have he := ScalarHomZero.scalarHomZeroCompatibility.{c, v, r} J A (B n)
      (α.app (op n)) (σ n) a (d.levelClosed n) aModels (d.levelTensorModels n) (ν n) hm
      (s.finite A) (s.finite (B n))
      (ordinarySectionsIso.{c, v, r} J A) (ordinarySectionsIso.{c, v, r} J (B n))
      hoA
      hoB
      (sectionsH0Comparison.{c, v, r} J A (s.finite A))
      (sectionsH0Comparison.{c, v, r} J (B n) (s.finite (B n)))
      (sectionsH0Comparison_unit.{c, v, r} J A (s.finite A))
      (sectionsH0Comparison_unit.{c, v, r} J (B n) (s.finite (B n)))
      (s.scalar (α.app (op n))) (_hs.scalar_unit (α.app (op n)))
      P (L.obj N) ((e.{c, v, max c v r} J B τ n).obj N) ((π n).app N) h
    refine he.trans ?_
    rw [(σ n).adjunction.homEquiv_naturality_left_symm]
    rw [projection_counit adj (e.{c, v, max c v r} J B τ n) (σ n).adjunction
      (ρ n) (π n) (fun X ↦ _hunit X n) N]
    rfl

end SheafOfModules.EnrichedSequenceProjection

