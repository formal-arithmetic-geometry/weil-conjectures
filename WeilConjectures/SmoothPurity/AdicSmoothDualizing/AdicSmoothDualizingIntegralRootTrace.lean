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

/-- Finite smooth trace in pulled-unit coordinates is the root-normalized integration.
This identity only involves published finite purity, root and scalar-unit comparisons;
no integral exceptional identification, reconstruction map or normalization is an input.
Source: corollary finite-normalization paragraph and diagonal purity unit specialization
(blueprint: lem-pur-adic-smooth-dualizing-integral-root-trace).

Proof: expand integralFiniteTrace. The normalized completed-unit pullback comparison
and the scalar-adjunction unit identify reduction of its source comparison with
the finite pulled coefficient unit. Naturality of finite smooth purity in that
coefficient unit moves its coefficient reduction to the target. Its ordinary-unit
presentation formula identifies the finite purity map with inverse diagonal purity
under pullback of the regular module and the tensor unitor. Thus its compact-support
image followed by the exceptional counit is exactly finiteIntegration. On local
primitive-root tensors the remaining source map is the projection defining
lineProjection, followed by finitePowerComparison.inv; the tensor universal property
identifies this with twistReduction. At power zero this is the regular coefficient
projection and shift-zero unitor. Reassociate the support and scalar isomorphisms
and cancel finiteReductionIso with its inverse. These are the two displayed sides.
All exponents are n+1; the tensor-unit argument also treats d=0 and the empty scheme. -/
theorem integralFiniteTrace_root_normalization (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (core : CompletedUnitPullback.Core P.coefficients.l P.extension
      (X ↘ Spec (.of P.field.k))) (n : ℕ) :
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).app
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).map
          (twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P X n d =
    integralFiniteTrace P X d core n ≫
      twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0 := by
  sorry

end WeilConjectures.AdicSmoothDualizing
