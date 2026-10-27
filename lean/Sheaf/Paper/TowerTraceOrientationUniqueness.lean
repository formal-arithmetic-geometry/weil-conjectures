/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.TowerTracePurityComparisonData

/-! # TowerTraceOrientationUniqueness

Source: latest blueprint, smooth purity and coefficient transport.
(blueprint: lem-pur-tower-trace-orientation-uniqueness). -/

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

/-- Two rank-one unit orientations with the prescribed reductions coincide.
Source: latest blueprint, tower-gamma proof (1), through integral orientation
reduction injectivity (blueprint: lem-pur-tower-trace-orientation-uniqueness).

Proof:
Regard the Tate line and the coefficient unit as objects of the complete
constructible full subcategories, using lineTor and core.admissibleY. Identify
their underlying complexes with the shifted single Tate line and the degree-zero
completed unit. Apply reduction_injectivity to the realized adjunction of m.
Transfer the specified exceptional target through its counit-preserving comparison.
Its rho evaluations, after the normalized finite right-adjoint comparisons, are
exactly scalarReductionDerivedExtension of sourceUnitIso.hom followed by g or h.
The hypotheses set both to the same finite purity map at every level. The finite
right comparisons and the source-unit comparison are isomorphisms, so cancelling
them gives equality of the rho families. Injectivity gives equality in the full
subcategory; taking underlying morphisms and cancelling sourceUnitIso gives g=h.
Only the rank-one single-complex injectivity is used, not faithfulness of level
reductions on arbitrary derived morphisms. -/
theorem prescribed_orientations_unique [QuasiCompact (j ≫ p)]
    (S : ConstructibleExceptionalCoefficients.RingSystem P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p))
    (M : FieldShriekSystem.Models P) (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P M E j p d) (A : Stage P j p d S M E m)
    (g h : PurUnitTrace.tateUnit P.field P.coefficients E.val d X ⟶
      ((S.operation (SpTowerGamma.factorization j p) (.integral { carrier := E.val })).G.obj
        ⟨_, A.core.admissibleY.1⟩).obj)
    (hg : PrescribedUnitReductions P j p d S M E m A g)
    (hh : PrescribedUnitReductions P j p d S M E m A h) : g = h := by
  sorry

end WeilConjectures.TowerTracePurityComparison
