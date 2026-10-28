/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.WeilPurityEquivarianceData

/-! # The completed integral purity composite is the geometric counit mate

Source: current blueprint, thm-pur-weil-equivariance-of-purity-and-trace, Steps 1, 3 and 5.
(blueprint: lem-pur-integral-equivariance-mate). -/

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

/-- Before choosing a strict Weil datum, the inverse-purity composite is the counit
mate of the canonical completed compact-support exchange.
Source: the equivariance proof, Steps 1, 3 and 5, and integral geometric comparison
realization, exceptional-transpose clause
(blueprint: lem-pur-integral-equivariance-mate).

Proof:
Reduce K to its whole normalized constructible coefficient tower. Apply the tower
geometric purity mate theorem to the semilinear Frobenius square, retagging source
structure maps so that its horizontal arrows are linear over the base field.
The underlying sites and proper/open compactifications do not change. The tower
purity square identifies the exceptional mate with inverse pulled-back purity,
the independent pullback/tensor/Tate/shift comparison, and purity at the pulled
back input, in that order. The adjunction Hom equivalence identifies its image
under compact support followed by the counit with inverse support exchange
followed by the pulled-back counit.
Apply total derived inverse limit to this equality of whole-tower morphisms.
Integral geometric comparison realization identifies the normalized pullback,
root-line, tensor, shift and source-square comparisons with integralP and
integralB. Its exceptional-transpose and counit clauses carry the Hom-equivalence
equation to the completed adjunction. Use tower_trace_purity_comparison to
identify realized normalized purity with the specified integralGamma. Finally
conjugate by S.ring.integralLeft and the uniquely counit-preserving right-adjoint
comparison. Those same comparisons define integralBeta and the counit in the
statement; their units and inverses cancel. This gives the displayed equation
for every K, before selecting phi. The argument realizes tower equations and
never infers equality from separate finite evaluations. It includes zero K,
empty schemes and dimension zero. -/
theorem integralEquivariance_mate
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.frobeniusFiber Y₀).left) :
    (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).F.map
      (((integralP P X₀).mapIso (integralGamma P X₀ Y₀ f₀ d c₀ S K)).inv ≫
        (integralB P X₀ Y₀ f₀ d K).hom ≫
        (integralGamma P X₀ Y₀ f₀ d c₀ S ((integralP P Y₀).obj K)).hom) ≫
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          ((integralP P Y₀).obj K) =
    (integralBeta P X₀ Y₀ f₀ c₀ S
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K)).inv ≫
      (integralP P Y₀).map
        ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
          (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K) := by
  sorry

end WeilConjectures.PurityWeil
