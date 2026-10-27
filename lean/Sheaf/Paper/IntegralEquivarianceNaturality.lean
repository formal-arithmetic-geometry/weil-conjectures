/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.WeilPurityEquivarianceData

/-! # Naturality in the completed integral equivariance argument

Source: current blueprint, thm-pur-weil-equivariance-of-purity-and-trace, Steps 2 and 5.
(blueprint: lem-pur-integral-equivariance-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityWeil

variable (P : PurityFiniteSetting.{u})
  (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
variable (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := zlFiberMap P.field f₀))

/-- Naturality of the completed trace-transpose purity and of the canonical completed
compact-support exchange, on arbitrary finite-Tor integral morphisms.
Source: the equivariance proof, Steps 2 and 5, and normalized integral adjunction,
Purity and Normalization clauses
(blueprint: lem-pur-integral-equivariance-naturality).

Proof:
Use the normalized reduction/total-limit equivalence on X and Y. Its units and
counits identify every integral morphism with the realization of its entire
normalized reduction tower; no equality is tested by the separate evaluations.
Tower gamma is a natural transformation, so its naturality square is an equality
of tower morphisms. Apply total derived inverse limit. The specified source
realization identifies its source functor with completed pullback tensored with
the shifted completed Tate line, hence with integralH. The counit-preserving
right-adjoint comparison and tower_trace_purity_comparison identify the realized
purity components with integralGamma, the fixed trace-transpose construction.
Naturality of the reconstruction units cancels all inserted comparisons. This
proves the first equation for an arbitrary integral arrow a.
For the second equation use the actual proper/open exchange natural transformation.
The completed-to-ordinary Frobenius comparison, compact-support realization,
canonical semilinear proper/open exchange and inverse comparisons in
RationalWeilPurity.integralExchange are all natural transformations. Their
composite is natural. Conjugate by S.ring.integralLeft, which is natural, and
apply the faithful inclusions of the full constructible and finite-Tor
subcategories. The resulting components are exactly integralBeta, proving the
second equation. No lattice, Frobenius-fixed object, or finite-level faithfulness
is assumed. The argument includes the zero object, empty schemes and d = 0. -/
theorem integralEquivariance_naturality :
    (∀ {K L : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
        (P.frobeniusFiber Y₀).left} (a : K ⟶ L),
      (integralGamma P X₀ Y₀ f₀ d c₀ S K).hom ≫
          (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
            (.integral (AdicSmoothDualizing.fieldStage P))).G.map a =
        (integralH P (P.frobeniusMap f₀) d).map a ≫
          (integralGamma P X₀ Y₀ f₀ d c₀ S L).hom) ∧
    (∀ {M N : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
        (P.frobeniusFiber X₀).left} (a : M ⟶ N),
      (integralP P Y₀).map
          ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
            (.integral (AdicSmoothDualizing.fieldStage P))).F.map a) ≫
        (integralBeta P X₀ Y₀ f₀ c₀ S N).hom =
      (integralBeta P X₀ Y₀ f₀ c₀ S M).hom ≫
        (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
          (.integral (AdicSmoothDualizing.fieldStage P))).F.map ((integralP P X₀).map a)) := by
  sorry

end WeilConjectures.PurityWeil
