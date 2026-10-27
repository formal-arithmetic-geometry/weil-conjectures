/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.TowerTracePurityComparisonData

/-! # TowerTraceCanonicalIntegral

Source: latest blueprint, smooth purity and coefficient transport.
(blueprint: lem-pur-tower-trace-canonical-integral). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.TowerTracePurityComparison

variable (P : PurityFiniteSetting.{u})

variable {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))]
  (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]

/-- The ordinary integral representative used by rationalIso is the completed
trace transpose, in the normalized tensor-source coordinates.
Source: latest blueprint, purity transport proof Steps 1--2 and tower-gamma (2).
(blueprint: lem-pur-tower-trace-canonical-integral).

Proof:
Transport the unit orientation through the canonical Tate-line and coefficient-unit
identifications of RationalSmoothPurityCanonical. Its prescribed finite reductions
and the counit normalization identify its trace with the normalized finite smooth
trace: at each quotient this is finiteIntegration_smoothPurityMap. Thus
integralMap_eq_adicTraceTranspose replaces the canonical orientation by this one.
Compare the resulting ordinary projection word with adicTraceMap. Use the
augmentation-defined ordinary-to-completed tensor comparison; its isomorphism on
the indicated finite-Tor inputs follows from the recorded completionIso. The
projection comparison is natural for this augmentation and the same proper/open
factorization. Its inverse therefore carries the ordinary inverse projection to
the inverse adic projection. IsUnitNormalized identifies the coefficient-unit
multiplication and the right unitor, while IsJNormalized identifies the source
comparison on the fixed K-flat line complex. The two compact-support words agree.
Apply the specified constructible adjunction homEquiv to that equality and take
underlying morphisms. No faithfulness of arbitrary finite evaluations is used. -/
theorem canonical_integral_transpose [QuasiCompact (j ≫ p)]
    [IsSeparated (j ≫ p)] [LocallyOfFiniteType (j ≫ p)]
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
    (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p))
    (M : FieldShriekSystem.Models P) (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P M E j p d)
    (A : Stage P j p d S.ring M E m)
    (hA : PrescribedUnitReductions P j p d S.ring M E m A
      (orientation P j p d S.ring M E m A))
    [IsIso (orientation P j p d S.ring M E m A)]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y) :
    (RationalSmoothPurityCanonical.integralMap (atField P E) (j ≫ p)
      (SpTowerGamma.factorization j p) S d K).hom =
      adicTranspose P.field P.coefficients E.val (j ≫ p) S.ring
        (SpTowerGamma.factorization j p) ⟨_, A.tensorTor K⟩ K
        (adicTraceMap P.coefficients.l E.val A.models A.openComparison
          (SpTowerGamma.factorization j p)
          (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) K.obj
          (A.completionIso K) (A.projectionIso K)
          (counitTrace P j p d S.ring M E m A
            (orientation P j p d S.ring M E m A) ≫ A.unitIso.hom)) := by
  sorry

end WeilConjectures.TowerTracePurityComparison
