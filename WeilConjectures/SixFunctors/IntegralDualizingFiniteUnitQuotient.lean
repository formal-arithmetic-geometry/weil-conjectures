/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData

/-! # The finite coefficient-unit quotient in realization coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The realized scalar-adjunction unit on the finite coefficient unit.
Source: Stacks 07A4; finite coefficient counit normalization.
(blueprint: def-coef-finite-unit-quotient). -/
def integralDualizingFiniteUnitQuotient (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (finiteDualizingRealization l E W m).obj
        (Etale.constantComplex (finiteDualizingCoeff l E m) W) ⟶
      (normalizedDVRRes l E W h).obj
        ((finiteDualizingRealization l E W n).obj
          (Etale.constantComplex (finiteDualizingCoeff l E n) W)) :=
  (finiteDualizingRealization l E W m).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (finiteDualizingQuotient l E h))).homEquiv _ _
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) W).hom) ≫
    (finiteDualizingRealizationRestriction l E W h).inv.app
      (Etale.constantComplex (finiteDualizingCoeff l E n) W)

end WeilConjectures
