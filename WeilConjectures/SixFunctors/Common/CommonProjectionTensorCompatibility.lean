/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
import WeilConjectures.SixFunctors.Common.CommonProjectionProperFactor
import WeilConjectures.SixFunctors.Common.CommonProjectionOpenFactor

/-! # A shared tensor comparison for common-stage projection mates
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures
open ProjectionCoefficientTransport

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion preserves each compact-support projection through one tensor comparison,
independent of the compactification. No compactification comparison law, composition law
or invertibility of projection is assumed. -/
theorem commonProjectionTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    ∃ t : ∀ X : SixFunctorSpace D,
      Functor.uncurry.obj ((H.coefficientStages E₀).rationalTensor X) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀ ≅
        (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).prod
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀) ⋙
          Functor.uncurry.obj (H.commonStageTensor X),
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).map
            (compactSupportProjectionComponent (H.coefficientStages E₀).rationalExchange
              f c K L) ≫
          (target (H.commonStageComparison E₀) t f c K L).hom =
        (source (H.commonStageComparison E₀) t f c K L).hom ≫
          compactSupportProjectionComponent H.commonStageExchange f c
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L) := by
  refine ⟨commonProjectionTensorComparison H E₀, ?_⟩
  intro X Y f c K L
  let Q := compactSupportProjectionSquare f c
  exact projection_preserved_of_factors (H.commonStageComparison E₀)
    (commonProjectionTensorComparison H E₀)
    ((H.coefficientStages E₀).rationalExchange Q) (H.commonStageExchange Q) K L
    (commonProjectionProperFactor H E₀ Q K L)
    (commonProjectionOpenFactor H E₀ Q K L)

end WeilConjectures
