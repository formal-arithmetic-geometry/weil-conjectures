/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.CanonicalCoefficientRepresentativeLaws
import Sheaf.Paper.CanonicalCoefficientCompositionLaws

/-! # Coherent reduction with the fixed integral closed tensor

Source: Stacks 06YS, 07A4, 08JD and 0941, and step 1 of the compatible
open-tensor context construction. This is the presentation-normalization refinement
of the coherent coefficient calculus, on a single scheme.
(blueprint: lem-pur-canonical-integral-evaluation-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures
section CategoricalComposition
variable {A : Type*} {B : Type*} [Category A] [Category B]
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

namespace CanonicalCoefficient

/-- The new quotient calculus has the old adjunctions and the conjugated tensor maps. -/
private def quotient (S : CoefficientDerivedSystemFibers l E W) :
    CoefficientFiniteQuotientCalculus l E W (tensors l E W
      S.toCoefficientDerivedSystemTensors) where
  toCoefficientFiniteQuotientData := quotientData l E W S.toCoefficientDerivedSystemTensors
    S.quotientCalculus.toCoefficientFiniteQuotientData
  ordinary_unit := S.quotientCalculus.ordinary_unit
  unit_model := S.quotientCalculus.unit_model
  tensor_model := (representativeLaws l E W S).quotient_tensor

/-- Reuse all non-tensor data; transport the actual fiber and base-change equations. -/
private def fibers (S : CoefficientDerivedSystemFibers l E W) :
    CoefficientDerivedSystemFibers l E W where
  toCoefficientDerivedSystemReduction := reduction l E W S.toCoefficientDerivedSystemReduction
  reductionTensor_normalization := (representativeLaws l E W S).reduction_tensor
  finiteTensor_normalization := (representativeLaws l E W S).finite_tensor
  evaluationTensor_normalization := (representativeLaws l E W S).evaluation_tensor
  reductionTensor_evaluation := (representativeLaws l E W S).reduction_evaluation
  quotientCalculus := quotient l E W S
  reduction_compatible :=
    { naturality := by
        intro P Q P' Q' f g
        dsimp only [reduction]
        simpa only [baseChange_eq] using S.reduction_compatible.naturality P Q P' Q' f g
      transpose := transpose_eq _ _ _ _ _ _ S.reduction_compatible
      composition := (compositionLaws l E W S).1 }
  finite_compatible n :=
    { naturality := by
        intro P Q P' Q' f g
        dsimp only [reduction]
        simpa only [baseChange_eq] using (S.finite_compatible n).naturality P Q P' Q' f g
      transpose := transpose_eq _ _ _ _ _ _ (S.finite_compatible n)
      composition := (compositionLaws l E W S).2 n }
  fiberHom := S.fiberHom
  fiber_evaluation := by
    intro M N hM hN n
    exact fiberEvaluation _ _ _ _ _ _ M N (S.fiberHom M N hM hN n).hom
      (S.fiber_evaluation M N hM hN n)
  fiber_naturality := S.fiber_naturality
  fiber_transition := by
    intro M N hM hN m n h
    have hh := S.fiber_transition M N hM hN h
    dsimp only [coefficientFiniteQuotientHomComparison, quotient, quotientData, reduction,
      coefficientSequenceNormalizationIso, coefficientSequenceTransitionAdjoint] at hh ⊢
    simpa only [baseChange_eq] using hh
  beta_evaluation := by
    intro P Q n
    dsimp only [reduction]
    simpa only [baseChange_eq] using S.beta_evaluation P Q n
  isIso_iff_evaluations := S.isIso_iff_evaluations
  globalEvaluation := S.globalEvaluation

/-- Global-limit data are kept literally, and enriched invertibility is categorical. -/
private def calculus (S : CoefficientDerivedSystemCalculus l E W) :
    CoefficientDerivedSystemCalculus l E W where
  toCoefficientDerivedSystemFibers := fibers l E W S.toCoefficientDerivedSystemFibers
  enriched_isIso := fun P N _ ↦ coefficientClosedEnriched_isIso
    (fibers l E W S.toCoefficientDerivedSystemFibers).integralClosed
    (fibers l E W S.toCoefficientDerivedSystemFibers).systemClosed
    S.reduction S.adjunction
    (fibers l E W S.toCoefficientDerivedSystemFibers).reductionTensor P N
  globalLimit := S.globalLimit

private theorem gamma_hom (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    ((calculus l E W S).gamma l E W P N hN).hom = (S.gamma l E W P N hN).hom := by
  dsimp only [CoefficientDerivedSystemCalculus.gamma, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [calculus, fibers, reduction, asIso_hom, Iso.app_hom]
  rw [enriched_eq]

private def resolutionCoherence (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S) :
    CoefficientDerivedSystemResolutionCoherence l E W (calculus l E W S) where
  toCoefficientDerivedSystemScalarCoherence := D.toCoefficientDerivedSystemScalarCoherence
  systemSectionsEvaluation := D.systemSectionsEvaluation
  globalEvaluation_model := D.globalEvaluation_model
  globalLimit_model := D.globalLimit_model

end CanonicalCoefficient

/-- Choose the coherent reduction calculus with its integral closed structure literally
equal to the fixed normalized duality structure. No open immersion, ordinary reduction
model, completion model, completion comparison or open comparison occurs here.

Source: Stacks 06YS, 07A4, 08JD and 0941; the coefficient-calculus construction
and step 1 of lem-pur-completed-open-tensor-context.
(blueprint: lem-pur-canonical-integral-evaluation-calculus).

Proof: start with the existing coherent calculus. CanonicalCoefficient.tensors fixes
its integral closed field to IntegralOnSlice.duality.closed and its sequence and
finite closed fields to normalized ringed-site duality structures. Transport each
old tensor-model comparison by the evaluation-preserving adjoint comparison;
comparison_transpose proves its ordinary uncurrying with the same chain map.
Conjugate each tensor comparison mu for F by F(a inverse); mu; b, retaining the
reduction functor, adjunction, finite evaluations and all non-tensor quotient data.
CanonicalCoefficient.representativeLaws proves the five representative equations
by inverse cancellation and naturality, with the same strict complexes and maps.

CanonicalCoefficient.baseChange_eq identifies the new base-change morphism with
the old one. Thus its naturality, transpose formula, quotient transition formula,
fiber evaluation and beta evaluation transport. Apply compositionLaws for the
internal-composition equations on the fixed normalized associators. This is the
only separate internal-composition input; it asserts no existence of a calculus.
Assemble the new fiber record with the old fiber Hom and global evaluations.

Keep the old globalLimit and resolution coherence. The enriched map is unchanged
by enriched_eq, so gamma.hom is literally the old morphism. Its projection,
naturality and degree-zero Hom equations transfer. Enriched invertibility is
coefficientClosedEnriched_isIso. Prove mapping composition by naturality of the
reduction adjunction and tensor comparison (parameter_composition). Assemble the
coherence record. The integral closed equality is reflexivity. These arguments
include empty schemes, zero objects and unbounded complexes; no invertibility
assumption on l on W is used. -/
theorem canonicalIntegralEvaluationCalculus :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S),
      (IntegralOnSlice.duality l E W none).closed = S.integralClosed := by
  obtain ⟨S, ⟨H⟩⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  let T := CanonicalCoefficient.calculus l E W S
  let D := CanonicalCoefficient.resolutionCoherence l E W S
    H.toCoefficientDerivedSystemResolutionCoherence
  refine ⟨T, ?_, rfl⟩
  refine {
    toCoefficientDerivedSystemResolutionCoherence := D
    finite_enriched_isIso := ?_
    gamma_projection := ?_
    gamma_naturality := ?_
    hom_projection := ?_
    composition := ?_ }
  · intro n P M
    exact coefficientClosedEnriched_isIso T.integralClosed (T.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
      (T.finiteTensor n) P M
  · intro P N hN n
    dsimp only [T, D, CanonicalCoefficient.resolutionCoherence]
    rw [CanonicalCoefficient.gamma_hom]
    dsimp only [CanonicalCoefficient.calculus, CanonicalCoefficient.fibers,
      CanonicalCoefficient.reduction]
    rw [CanonicalCoefficient.enriched_eq]
    exact H.gamma_projection P N hN n
  · intro P P' N N' hN hN' a b
    dsimp only [T]
    rw [CanonicalCoefficient.gamma_hom, CanonicalCoefficient.gamma_hom]
    exact H.gamma_naturality P P' N N' hN hN' a b
  · intro P N hN h n
    dsimp only [T, coefficientGammaZeroMap, coefficientGammaZero]
    rw [CanonicalCoefficient.gamma_hom]
    exact H.hom_projection P N hN h n
  · intro T' U P N N' f g
    exact parameter_composition T.integralClosed T.systemClosed T.reduction T.adjunction
      T.reductionTensor T' U P N N' f g

end WeilConjectures
