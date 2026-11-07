/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import Submission.WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import Submission.WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck

public import Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
public import Submission.WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import Submission.WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemResolutionModels
import Submission.WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemProjectionFormulas

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Assembly of the coherent derived coefficient-system evaluation calculus

Source: Stacks 06YS, 0A95, 0941, 079P; the sequence and enriched-adjunction route
(blueprint: lem-coef-derived-system-evaluation-calculus). -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section CategoricalComposition

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

private theorem parameter_composition (T U P : A) (N N' : B)
    (f : SA.tensor.obj (T, P) ⟶ G.obj N)
    (g : SB.tensor.obj (F.obj U, N) ⟶ N') :
    adj.homEquiv _ _
      (μ.hom.app (U, SA.tensor.obj (T, P)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 _) ((adj.homEquiv _ _).symm f)) ≫ g) =
    SA.tensor.map (Prod.mkHom (𝟙 U) f) ≫
      adj.homEquiv _ _
        (μ.hom.app (U, G.obj N) ≫
          SB.tensor.map (Prod.mkHom (𝟙 _) (adj.counit.app N))) ≫ G.map g := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  congr 1
  rw [adj.homEquiv_counit]
  have hμ := μ.hom.naturality (Prod.mkHom (𝟙 U) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  symm
  calc
    _ = (F.map (SA.tensor.map (Prod.mkHom (𝟙 U) f)) ≫ μ.hom.app (U, G.obj N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 _) (adj.counit.app N)) ≫ g := by
      simp only [Category.assoc]
    _ = (μ.hom.app (U, SA.tensor.obj (T, P)) ≫
        SB.tensor.map (Prod.mkHom (F.map (𝟙 U)) (F.map f))) ≫
        SB.tensor.map (Prod.mkHom (𝟙 _) (adj.counit.app N)) ≫ g := by rw [hμ]
    _ = _ := by
      have hp : Prod.mkHom (F.map (𝟙 U)) (F.map f) ≫
          Prod.mkHom (𝟙 (F.obj U)) (adj.counit.app N) =
          Prod.mkHom (𝟙 (F.obj U)) (F.map f ≫ adj.counit.app N) :=
        Prod.hom_ext ((Category.comp_id _).trans (F.map_id U)) rfl
      have hm := (SB.tensor.map_comp (Prod.mkHom (F.map (𝟙 U)) (F.map f))
        (Prod.mkHom (𝟙 (F.obj U)) (adj.counit.app N))).symm.trans
          (congrArg SB.tensor.map hp)
      simpa only [Category.assoc] using
        congrArg (fun z ↦ μ.hom.app (U, SA.tensor.obj (T, P)) ≫ z ≫ g) hm

end CategoricalComposition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The full coherent derived reduction, limit adjunction and fiberwise evaluation calculus.
Source: Stacks 06YS, 0A95, 0941, 079P; the enriched varying-coefficient comparison
is the agent-formulated construction in the node
(blueprint: lem-coef-derived-system-evaluation-calculus).

Proof, following the node step by step:
1. By coefficientDerivedSystemResolutionModels (lem-coef-derived-system-resolution-models)
choose normalized fibers F, the global-limit comparison kappa, the resolution coherence D
and the projection-model equations H. Construct S from F and kappa; its enriched_isIso field
is coefficientClosedEnriched_isIso: the evaluation-defined enriched adjunct is the inverse of
the five-Hom-bijection comparison ClosedScalarHom.iso (lem-sfb-closed-scalar-hom-comparison).
2. coefficientDerivedSystemProjectionFormulas (lem-coef-derived-system-projection-formulas)
applied to S, D and H gives the gamma projection and Hom-zero projection fields.
3. Finite enriched invertibility is coefficientClosedEnriched_isIso for the finite scalar
adjunction and its tensor comparison. Gamma naturality: apply integral sections to
coefficientClosedEnriched_naturality, then naturality of kappa.
4. Composition: by left and right naturality of the reduction adjunction Hom bijection,
both sides are adjuncts; naturality of the tensor comparison at (1, f) and functoriality
of the system tensor identify them, the right side being tensorLimitMap, the counit mate.
Steps 3 and 4 are elementary and fully proved here. No reconstruction or invertibility of
beta or the reconstruction unit on arbitrary inputs is claimed. -/
theorem coefficientDerivedSystemEvaluationCalculus :
    ∃ S : CoefficientDerivedSystemCalculus l E W,
      Nonempty (CoefficientDerivedSystemCoherence l E W S) := by
  obtain ⟨F, κ, D, H⟩ := coefficientDerivedSystemResolutionModels l E W
  let S : CoefficientDerivedSystemCalculus l E W :=
    { toCoefficientDerivedSystemFibers := F
      enriched_isIso := fun P N _ ↦ coefficientClosedEnriched_isIso
        F.integralClosed F.systemClosed F.reduction F.adjunction F.reductionTensor P N
      globalLimit := κ }
  change CoefficientDerivedSystemResolutionCoherence l E W S at D
  change CoefficientDerivedSystemProjectionModels l E W S D at H
  obtain ⟨hγ, h₀⟩ := coefficientDerivedSystemProjectionFormulas l E W S D H
  refine ⟨S, ⟨{
    toCoefficientDerivedSystemResolutionCoherence := D
    finite_enriched_isIso := ?_
    gamma_projection := hγ
    gamma_naturality := ?_
    hom_projection := h₀
    composition := ?_ }⟩⟩
  · intro n P M
    exact coefficientClosedEnriched_isIso S.integralClosed (S.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
      (S.finiteTensor n) P M
  · intro P P' N N' hN hN' a b
    dsimp only [CoefficientDerivedSystemCalculus.gamma, Iso.trans_hom, Functor.mapIso_hom]
    change (coefficientIntegralSections l E W).map
        ((coefficientIntegralInternalHom l E W).map
          (Prod.mkHom a.op ((coefficientSequenceLimit l E W).map b))) ≫
        ((coefficientIntegralSections l E W).map
          (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
            S.adjunction S.reductionTensor P' N') ≫ S.globalLimit.hom.app _) =
      ((coefficientIntegralSections l E W).map
          (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
            S.adjunction S.reductionTensor P N) ≫ S.globalLimit.hom.app _) ≫
        coefficientMappingLimit.map
          ((coefficientSequenceGlobalHom l E W).map (Prod.mkHom (S.reduction.map a).op b))
    rw [← Category.assoc, ← Functor.map_comp,
      coefficientClosedEnriched_naturality, Functor.map_comp, Category.assoc]
    simpa only [coefficientSequenceGlobalHom, Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ (coefficientIntegralSections l E W).map
      (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
        S.adjunction S.reductionTensor P N) ≫ z)
      (S.globalLimit.hom.naturality
        ((coefficientSequenceInternalHom l E W).map (Prod.mkHom (S.reduction.map a).op b)))
  · intro T U P N N' f g
    exact parameter_composition S.integralClosed S.systemClosed S.reduction S.adjunction
      S.reductionTensor T U P N N' f g

end WeilConjectures
