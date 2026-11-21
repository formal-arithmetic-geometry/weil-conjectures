/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralSupportPreservation
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralSupportAdjointOfPreservation

/-! # A right adjoint to the restricted integral compact-support functor

## References

* Zheng, Construction 5.25 and Propositions 5.24 and 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/-- Preservation and right-adjoint existence for one integral compact-support functor. -/
theorem exists_integral_support_adjoint (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∃ hpres : ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
      finiteTorConstructibleIntegral l E.carrier Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj K.obj),
    ((finiteTorConstructibleIntegral l E.carrier Y).lift
      ((finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c)
      hpres).IsLeftAdjoint  := by
  exact ⟨integral_support_preservation l D _hl f c E,
    integral_support_adjoint_of_preservation l D _hl f c E
      (integral_support_preservation l D _hl f c E)⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
