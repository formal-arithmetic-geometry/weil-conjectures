/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTracePurityComparisonData

/-! # TowerTraceNormalizedPresentations

Source: latest blueprint, smooth purity and coefficient transport.
(blueprint: lem-pur-tower-trace-normalized-presentations). -/

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

/-- Simultaneous normalized tower presentations, with their counit adjunct formula.
Source: latest blueprint, tower-gamma proof (1)--(2) and field-extension-towers (2).
(blueprint: lem-pur-tower-trace-normalized-presentations).

Proof:
Choose the field-extension tower models for the fixed compactification. At every
finite field apply realized_tower_purity_transpose. Transport its realization to
these models using the reconstruction equivalence and the counit-preserving unique
comparison of right adjoints. Both source comparisons are the maps on the fixed
K-flat representatives, so their equality follows by that normalization. The finite
exceptional comparison is fixed by its Hom normalization. Take the line and unit
K-flat models, their normalized unit and tensor comparisons, and the ordinary
coefficient comparison normalized by multiplication. The projection formula and
finite-Tor stability supply the remaining Stage fields. The finite reduction
identity of the realized transpose, at the unit and after sourceUnitIso, gives the
prescribed reductions; its invertibility gives invertibility of the orientation.
Finally its projection/counit identity, transported through the normalized tensor
source and left realization, is precisely the inverse homEquiv formula displayed
below. The unique right-adjoint comparison preserves the counit, so this formula
holds for the specified S, not just for the realized exceptional functor. -/
theorem normalized_presentations [QuasiCompact (j ≫ p)]
    [CompactSpace X] [QuasiSeparatedSpace Y]
    (S : ConstructibleExceptionalCoefficients.RingSystem P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := j ≫ p)) :
    ∃ (M : FieldShriekSystem.Models P) (R : FieldExtensionTowers.Result P M j p d)
      (A : ∀ E : FieldShriekSystem.Index P, Stage P j p d S M E (R.model E)),
      (∀ E : FieldShriekSystem.Index P,
        PrescribedUnitReductions P j p d S M E (R.model E) (A E)
          (orientation P j p d S M E (R.model E) (A E)) ∧
        IsIso (orientation P j p d S M E (R.model E) (A E))) ∧
      ∀ (E : FieldShriekSystem.Index P)
        (K : finiteTorConstructibleIntegralCategory P.coefficients.l E.val Y),
        ((S.operation (SpTowerGamma.factorization j p)
          (.integral { carrier := E.val })).adjunction.homEquiv
            ⟨_, (A E).tensorTor K⟩ K).symm
              (ObjectProperty.homMk ((A E).tensorSource.inv.app K ≫
                tower P j p d S M E (R.model E) (A E) K)) =
          ObjectProperty.homMk
            ((S.left (SpTowerGamma.factorization j p)
              (.integral { carrier := E.val })).hom.app ⟨_, (A E).tensorTor K⟩ ≫
              adicTraceMap P.coefficients.l E.val (A E).models (A E).openComparison
                (SpTowerGamma.factorization j p)
                (PurUnitTrace.tateUnit P.field P.coefficients E.val d X) K.obj
                ((A E).completionIso K) ((A E).projectionIso K)
                (counitTrace P j p d S M E (R.model E) (A E)
                  (orientation P j p d S M E (R.model E) (A E)) ≫ (A E).unitIso.hom)) := by
  sorry

end WeilConjectures.TowerTracePurityComparison
