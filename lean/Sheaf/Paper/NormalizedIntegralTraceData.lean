/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.TowerTracePurityComparisonData
import Sheaf.Paper.TowerTracePurityComparison

/-! # Integral traces at the specified base orientation

Source: tower-trace-purity-comparison, specialized to its own base orientation.
(blueprint: lem-pur-normalized-integral-trace-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
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

attribute [local irreducible] TowerTracePurityComparison.tower
  TowerTracePurityComparison.orientation TowerTracePurityComparison.counitTrace
  TowerTracePurityComparison.extendedTrace TowerTracePurityComparison.tracePurity
  WeilConjectures.RealizedTowerPurity.restrictedAdjunction
  WeilConjectures.RealizedTowerPurity.specifiedAdjunction
  SpTowerCalculus.realization SpIntegralAdjunction.limit
  sfRationalScalarExtension rationalDerivedPullback rationalDerivedTensor
  ScalarLocalization.category
  TowerTracePurityComparison.commonImage
  RationalSmoothPurityCanonical.integralMap RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.sourceScalar RationalSmoothPurityCanonical.rationalSource
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category

/-- Simultaneous prescribed orientations, scalar traces and integral trace transposes,
using the actual base orientation of the same tower model system.
Source: latest blueprint, tower-trace-purity-comparison and purity-transport Steps 2--4.
(blueprint: lem-pur-normalized-integral-trace-data).

Proof: take the models and stages of tower_trace_purity_comparison. At the base
coefficient field its prescribed orientation is invertible, so use that orientation
itself as the input isomorphism g0. Its prescribed reductions are the theorem's own
unit reductions. The scalar-trace conclusion identifies the extended trace with the
counit trace at every finite field. Substitute this equality in the integral part
of the comparison conclusion. Retain those integral equations and the same model
system, stages and orientation certificates. This is specialization and projection
of the existing comparison, including d=0 and empty schemes. -/
theorem normalized_integral_trace_data
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
        TowerTracePurityComparison.Stage P j p d S.ring M E (R.model E)),
      (∀ E : FieldShriekSystem.Index P,
        TowerTracePurityComparison.PrescribedUnitReductions P j p d S.ring M E
          (R.model E) (T E)
          (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E)) ∧
        IsIso (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E))) ∧
      (∀ E : FieldShriekSystem.Index P,
        TowerTracePurityComparison.extendedTrace P j p d S.ring M E (R.model E) (T E)
            (TowerTracePurityComparison.counitTrace P j p d S.ring M
              (TowerTracePurityComparison.base P) (R.model (TowerTracePurityComparison.base P))
              (T (TowerTracePurityComparison.base P))
              (TowerTracePurityComparison.orientation P j p d S.ring M
                (TowerTracePurityComparison.base P)
                (R.model (TowerTracePurityComparison.base P))
                (T (TowerTracePurityComparison.base P)))) =
          TowerTracePurityComparison.counitTrace P j p d S.ring M E (R.model E) (T E)
            (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E))) ∧
      ∀ (E : FieldShriekSystem.Index P)
        (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y),
        TowerTracePurityComparison.tracePurity P j p d S.ring M E (R.model E) (T E)
            (TowerTracePurityComparison.counitTrace P j p d S.ring M E (R.model E) (T E)
              (TowerTracePurityComparison.orientation P j p d S.ring M E (R.model E) (T E))) K =
          TowerTracePurityComparison.tower P j p d S.ring M E (R.model E) (T E) K := by
  classical
  let : CompactSpace X := FieldExtensionTowers.compactSpace P X
  obtain ⟨M, R, T, hT, htrace⟩ :=
    TowerTracePurityComparison.tower_trace_purity_comparison P j p d S
  let E0 := TowerTracePurityComparison.base P
  let g0 := TowerTracePurityComparison.orientation P j p d S.ring M E0 (R.model E0) (T E0)
  let : IsIso g0 := (hT E0).2
  obtain ⟨_, hscalar, hpurity⟩ := htrace (asIso g0) (hT E0).1
  refine ⟨M, R, T, hT, hscalar, ?_⟩
  intro E K
  have h := (hpurity E K).1
  rw [hscalar E] at h
  exact h

end AlgebraicGeometry.ProEtale.TransportIntegralCounit
