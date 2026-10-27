/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntegralReductionTower
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CoefficientSystemScalarCalculus
public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData
import Sheaf.Paper.CoefficientDerivedSystemResolutionModels
import Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas

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
