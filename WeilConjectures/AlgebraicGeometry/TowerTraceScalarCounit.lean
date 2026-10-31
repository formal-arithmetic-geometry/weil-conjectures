/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTracePurityComparisonData

/-! # TowerTraceScalarCounit

Source: latest blueprint, smooth purity and coefficient transport.
(blueprint: lem-pur-tower-trace-scalar-counit). -/

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

/-- Extending the tower's unit counit trace gives its counit trace over E.
Source: latest blueprint, field-extension-towers proof (2), purity and counit
squares (blueprint: lem-pur-tower-trace-scalar-counit).

Proof:
Use R.integral from the base field to E. Its purity square sends the base tower
orientation to the E orientation through the normalized twisted-unit comparison;
its counit square sends the specified counit to the E counit. The right-adjoint
uniqueness comparison transfers both squares to S. In the extended trace, replace
the coefficient-unit multiplication and compact-support comparison by their
normalizing formulas in A.coefficients. Naturality moves the base orientation
through the inverse support comparison. Substitute the purity square and then the
counit square; cancel the twisted-unit comparison and its inverse. The resulting
word is S.left inverse, S.F of the E orientation, and S.counit, hence counitTrace.
The finite reduction hypotheses ensure that the orientations in these squares
are the prescribed ones, by rank-one reduction injectivity. Ordinary completed
scalar extension agrees with the strict tower extension by the finite-free
coefficient comparison, including ramified fields and the base inclusion. -/
theorem scalar_counit [QuasiCompact (j ≫ p)]
    [CompactSpace X] [QuasiSeparatedSpace Y]
    (S : ConstructibleExceptionalCoefficients.RingSystem P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p))
    (M : FieldShriekSystem.Models P) (R : FieldExtensionTowers.Result P M j p d)
    (A : ∀ E : FieldShriekSystem.Index P, Stage P j p d S M E (R.model E))
    (hA : ∀ E : FieldShriekSystem.Index P,
      PrescribedUnitReductions P j p d S M E (R.model E) (A E)
        (orientation P j p d S M E (R.model E) (A E)))
    (E : FieldShriekSystem.Index P) :
    extendedTrace P j p d S M E (R.model E) (A E)
        (counitTrace P j p d S M (base P) (R.model (base P)) (A (base P))
          (orientation P j p d S M (base P) (R.model (base P)) (A (base P)))) =
      counitTrace P j p d S M E (R.model E) (A E)
        (orientation P j p d S M E (R.model E) (A E)) := by
  sorry

end WeilConjectures.TowerTracePurityComparison
