/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralTraceCoordinates

/-! # Root normalization of reconstructed integral purity

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md.
(blueprint: lem-pur-adic-smooth-dualizing-integral-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicSmoothDualizing

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- A prescribed purity lift has the finite coefficient-valued counit trace.
The conclusion precedes all root-coordinate identifications and contains no finiteIntegration.
Source: purity transport Steps 2-3, exceptional coefficient comparison counit equation;
corollary proof Step 1
(blueprint: lem-pur-adic-smooth-dualizing-integral-counit-reduction).

Proof: write the ambient pairing as inverse S.left followed by the adjunction
transpose. Use S.comparison_normalized to move reduction past S.left. Expand the
transpose as compact support of g followed by the counit, and apply the comparison
counit identity. The finite right realization normal.counit changes its counit to
the published finite smooth exceptional counit. Naturality moves reduction of g
past compact support. Precompose the prescribed reduction equation with reduction
of integralUnitSourceComparison.inv, cancelling the inverse pair. The remaining
finite composite is coefficientValuedSmoothTrace by definition. Finally the
finiteReductionIso on the base converts back to pbc derived-extension coordinates.
Every map here is an actual adjunction or scalar realization map; no detection or
uniqueness is used. The argument includes relative dimension zero and empty schemes. -/
theorem integralCounit_prescribed_reductions
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (normal : PurUnitTrace.FiniteRightNormalization P.field P.coefficients P.extension
      (X ↘ Spec (.of P.field.k)) S.ring)
    (core : CompletedUnitPullback.Core P.coefficients.l P.extension
      (X ↘ Spec (.of P.field.k)))
    (g : integralTwist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0))
    (hg : PurUnitTrace.HasPrescribedReductions P.field P.coefficients P.extension
      (X ↘ Spec (.of P.field.k)) d S.ring normal
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)
      ((integralUnitSourceComparison P X d core).hom ≫ g.hom.hom)) :
    ∀ n : ℕ,
      (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map
          (integralCounitAmbient P X S d g.symm) = integralFiniteTrace P X d core n := by
  sorry

end WeilConjectures.AdicSmoothDualizing
