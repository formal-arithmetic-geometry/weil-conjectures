/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralTraceCoordinates
import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralCounitReduction
import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralRootTrace

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

/-- Prescribed finite purity reductions give the root-normalized integral integration.
This only compares the two published normalization formulas; the integral purity
isomorphism and its prescribed reductions are inputs.

Source: smooth-dualizing corollary proof, coefficient-unit application and final
coefficient-change clause
(blueprint: lem-pur-adic-smooth-dualizing-integral-normalization).

Proof: transpose the supplied purity arrow under the specified exceptional
adjunction. The normalized target comparison and the coefficient comparison's
counit equation identify the reduction of this transpose with the finite smooth
trace at the reduced unit. The normalized completed-unit multiplication identifies
the reduced unit with the finite regular coefficient sheaf. Its pulled-unit source
comparison and the tensor unitor identify the source with the shifted finite root
power. In these coordinates finite smooth purity at the unit is inverse diagonal
purity; composing with its counit is finiteIntegration. The root projection formula
for lineProjection, the scalar-adjunction unit, and finitePowerComparison identify
the resulting source map with twistReduction, including its even-shift comparison.
At the point, power zero uses the coefficient projection and shift-zero unitor.
Substitute these two identifications into the finite counit equation. Its two sides
are exactly the defining sides of IsNormalizedIntegralIntegration. This calculation
is valid at every positive exponent n+1, at d=0, and for the empty scheme. -/
theorem integralIdentification_normalized_of_prescribed
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
    IsNormalizedIntegralIntegration P X d (integralCounitAmbient P X S d g.symm) := by
  intro n
  exact (integralFiniteTrace_root_normalization P X d core n).trans
    (congrArg (fun t ↦ t ≫ twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0)
      (integralCounit_prescribed_reductions P X S d normal core g hg n).symm)

end WeilConjectures.AdicSmoothDualizing
