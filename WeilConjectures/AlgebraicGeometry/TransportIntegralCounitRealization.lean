/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitData
public import WeilConjectures.AlgebraicGeometry.TowerTracePurityComparisonData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompositionFactors
public import WeilConjectures.AlgebraicGeometry.SmoothPurityBaseChangeFactors
public import WeilConjectures.AlgebraicGeometry.TransportIntegralBaseChangeRealization
public import WeilConjectures.AlgebraicGeometry.TransportIntegralStageConstruction
public import WeilConjectures.AlgebraicGeometry.TransportCondensedStageRealization
public import WeilConjectures.AlgebraicGeometry.TransportIntegralChartRealization
public import WeilConjectures.AlgebraicGeometry.TransportIntegralCompositionRealization
import WeilConjectures.AlgebraicGeometry.NormalizedIntegralTraceData
import WeilConjectures.AlgebraicGeometry.FixedPresentationUniformizerReductions

/-! # Integral realization with the specified smooth counit

Source: purity-transport, the existing integral realization argument.
(blueprint: lem-pur-transport-integral-counit-realization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [QuasiSeparatedSpace Y]

attribute [local irreducible] TowerTracePurityComparison.tower
  TowerTracePurityComparison.orientation TowerTracePurityComparison.counitTrace
  TowerTracePurityComparison.extendedTrace TowerTracePurityComparison.tracePurity
  WeilConjectures.RealizedTowerPurity.restrictedAdjunction
  WeilConjectures.RealizedTowerPurity.specifiedAdjunction
  SpTowerCalculus.realization SpIntegralAdjunction.limit
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category

/-- Simultaneous integral realization for every finite coefficient field, with the
actual trace-transpose equality and every positive uniformizer reduction. The stage
records give the explicit Hom adjunction, fixed counit, finite reductions and condensed
realization; coefficient_stage gives the specified scalar comparison. The geometric
whole-system equations are composition_realization and baseChange_realization, and
the chart counits are chart_realization.
Source: latest blueprint, purity-transport Steps 2--4, integral case.
(blueprint: lem-pur-transport-integral-counit-realization).

Proof: use the supplied Noetherian structures on X and Y. Integral-models identifies
condensed integral Dctf with the completed
constructible category; normalized-equivalence identifies that category with the
normalized strict towers by actual reduction and total limit. The direct-image-tower
comparison identifies the left adjoint with the same ambient compactification
composite. Integral-adjunction-bijection gives its Hom bijection and tower-gamma gives
the actual realized isomorphism. Integral_stage transports this adjunction, with
Phi(h) = B(h) gammaH inverse and inverse Phi(a) = F(a gammaH) epsilonH. Its counit is
F(gammaH) epsilonH. Right-adjoint uniqueness identifies H with the chosen G, preserving
that counit, and hence gives F(gammaT) epsilon = t.
Tower-trace-purity-comparison identifies this actual whole-tower map with the coherent
trace transpose and identifies its unit trace with scalar extension of the base trace.
Realized-transpose identifies all uniformizer reductions using the canonical
arithmetic cofinal comparison: ell-power levels are the ramification-stride subsequence,
and every positive uniformizer level is reached by quotient reassociation. These are
equalities of actual morphisms, independent of the chosen sufficiently large level.
Field-extension-towers preserves the actual gamma, unit and counit; substitution gives
coefficient_stage, with transitivity inherited from its left and source cocycles.
For composition and Cartesian base change, apply normalized reconstruction calculus
to the actual tower diagrams, as stated separately below; no uniqueness of an arbitrary
coherent lift is used. Chart_realization identifies the counit with fibre sum followed
by the iterated projective-line integrations, including d = 0. -/
theorem integral_counit_realization
    [SmoothOfRelativeDimension d (j ≫ p)]
    [IsNoetherian X] [IsNoetherian Y]
    [QuasiCompact (j ≫ p)] [IsSeparated (j ≫ p)] [LocallyOfFiniteType (j ≫ p)]
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p)) :
    ∃ (M : FieldShriekSystem.Models P)
      (R : FieldExtensionTowers.Result P M j p d)
      (T : ∀ E : FieldShriekSystem.Index P,
        TowerTracePurityComparison.Stage P j p d S.ring M E (R.model E))
      (A : ∀ E : FieldShriekSystem.Index P, Stage P M j p d E (R.model E))
      (_C : ∀ E : FieldShriekSystem.Index P, CondensedStage P M j p d E (R.model E) (A E)),
      ∀ E : FieldShriekSystem.Index P,
        TowerTracePurityComparison.PrescribedUnitReductions P j p d S.ring M E
          (R.model E) (T E)
          (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E)) ∧
        IsIso (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E)) ∧
        TowerTracePurityComparison.extendedTrace P j p d S.ring M E (R.model E) (T E)
            (TowerTracePurityComparison.counitTrace P j p d S.ring M
              (TowerTracePurityComparison.base P) (R.model (TowerTracePurityComparison.base P))
              (T (TowerTracePurityComparison.base P))
              (TowerTracePurityComparison.orientation P j p d S.ring M
                (TowerTracePurityComparison.base P)
                (R.model (TowerTracePurityComparison.base P))
                (T (TowerTracePurityComparison.base P)))) =
          TowerTracePurityComparison.counitTrace P j p d S.ring M E (R.model E) (T E)
            (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E)) ∧
        (∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
          TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K =
            (R.model E).sourceNormalization.exactSource.hom.app
                ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val Y).obj K) ≫
              ((A E).gammaH.hom.app
                ((PurCompactSupport.finiteTorIntegralInclusion
                  P.coefficients.l E.val Y).obj K)).hom ≫
              (((WeilConjectures.RealizedTowerPurity.restrictedAdjunction
                P.coefficients.l E.val (SpTowerGamma.factorization j p)
                (R.model E).realization.support_closed _ (R.model E).realization.adjunction
                (T E).supportClosed (T E).rightClosed).rightAdjointUniq
                  (WeilConjectures.RealizedTowerPurity.specifiedAdjunction P.field P.coefficients
                    E.val (j ≫ p) S.ring (SpTowerGamma.factorization j p)
                    (T E).supportClosed)).hom.app K).hom ∧
          IsIso (TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K) ∧
          TowerTracePurityComparison.tracePurity P j p d S.ring M E (R.model E) (T E)
              (TowerTracePurityComparison.counitTrace P j p d S.ring M E (R.model E) (T E)
                (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E))) K =
            TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K) ∧
        ∃ e : ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y,
            (((S.ring.operation (SpTowerGamma.factorization j p)
              (.integral {carrier := E.val})).G.obj K).obj) ≅
              purAdicTarget P.field P.coefficients E.val (j ≫ p) K.obj,
          (∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) (n : ℕ),
            (scalarReductionDerivedExtension P.coefficients.l E.val X n).map (e K).hom ≫
                purAdicTargetReduction P.field P.coefficients E.val (j ≫ p) d
                  K.obj K.property n =
              WeilConjectures.RealizedTowerPurity.finiteReduction P.field P.coefficients
                E.val (j ≫ p) S.ring (SpTowerGamma.factorization j p) (T E).normal K n) ∧
          ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) (n : ℕ),
            (scalarReductionDerivedExtension P.coefficients.l E.val X n).map
                (TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K ≫
                  (e K).hom) ≫
                purAdicTargetReduction P.field P.coefficients E.val (j ≫ p) d
                  K.obj K.property n =
              purAdicSourceReduction P.field P.coefficients E.val (j ≫ p) d
                K.obj K.property n ≫
                (purAdicFiniteArrow P.field P.coefficients E.val (j ≫ p) d
                  K.obj K.property n).hom := by
  classical
  let : CompactSpace X := FieldExtensionTowers.compactSpace P X
  obtain ⟨M, R, T, hT, hscalar, hpurity⟩ :=
    normalized_integral_trace_data P j p d S
  let A : ∀ E : FieldShriekSystem.Index P, Stage P M j p d E (R.model E) :=
    fun E ↦ Classical.choice (integral_stage P M j p d E (R.model E))
  let C : ∀ E : FieldShriekSystem.Index P,
      CondensedStage P M j p d E (R.model E) (A E) :=
    fun E ↦ Classical.choice (condensed_stage P M j p d E (R.model E) (A E))
  refine ⟨M, R, T, A, C, ?_⟩
  intro E
  refine ⟨(hT E).1, (hT E).2, hscalar E, ?_,
    fixed_presentation_uniformizer_reductions P M j p d S.ring E (R.model E) (T E)
      (hT E).1 (hpurity E)⟩
  intro K
  have heq : TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K =
      (R.model E).sourceNormalization.exactSource.hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val Y).obj K) ≫
        ((A E).gammaH.hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E.val Y).obj K)).hom ≫
        (((WeilConjectures.RealizedTowerPurity.restrictedAdjunction
          P.coefficients.l E.val (SpTowerGamma.factorization j p)
          (R.model E).realization.support_closed _ (R.model E).realization.adjunction
          (T E).supportClosed (T E).rightClosed).rightAdjointUniq
            (WeilConjectures.RealizedTowerPurity.specifiedAdjunction P.field P.coefficients
              E.val (j ≫ p) S.ring (SpTowerGamma.factorization j p)
              (T E).supportClosed)).hom.app K).hom := by
    rw [(A E).gammaH_eq]
    unfold TowerTracePurityComparison.tower
      AlgebraicGeometry.ProEtale.RealizedTowerPurity.component
    rfl
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    infer_instance
  · exact hpurity E K


end AlgebraicGeometry.ProEtale.TransportIntegralCounit
