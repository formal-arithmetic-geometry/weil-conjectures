/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurUnitTrace.AdicUnitTraceReductionData

/-! # AdicUnitTraceTargetNormalization

Compatibility step for the unit-trace construction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.PurUnitTrace
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : RingSystem C.l C.Qbar D C.different (f := f))

/-- The specified exceptional adjunction and its counit-normalized finite realization
have the same reduction maps as the actual exceptional tower.

Source: purity transport Steps 2-3 and the parent unit-trace proof Step 1
(blueprint: lem-pur-unit-trace-target-normalization).

Proof: restrict the actual integral compact-support/exceptional adjunction to the
uniform finite-Tor subcategories. Transport its left adjoint along S.left and take
the unique right-adjoint comparison preserving the counit. Do the same at every
finite level using the finite exceptional adjunction and finiteImageIso. The latter
comparisons form normal.iso, and their defining counit equation is normal.counit.
The integral comparison gives e. Both its reduction and the exceptional tower's
published evaluation comparison are mates of the same compact-support reduction
map. The counit equation and injectivity of the exceptional Hom bijection identify
them, giving the displayed equation at every positive exponent. This argument
uses right-adjoint uniqueness, never uniqueness of arbitrary integral lifts. -/
theorem unit_trace_target_normalization :
    ∃ normal : FiniteRightNormalization D C E f S,
      ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
        ∃ e : purAdicTarget D C E f K.obj ≅ ((operation D C E f S).G.obj K).obj,
          ∀ n : ℕ, HEq
            ((scalarReductionDerivedExtension C.l E X n).map e.hom ≫
              targetReduction D C E f S normal K n)
            (purAdicTargetReduction D C E f d K.obj K.property n) := by sorry

end WeilConjectures.PurUnitTrace
