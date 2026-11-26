/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChangeData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.CoefficientPresentationIntegralMapIndependence

/-! # Integral scalar-mate steps for native compact support

## References

* [Bhatt--Scholze, Section 6.8, Lemma 6.8.2]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
/-- The normalized finite integral inclusion is compatible with every scheme pullback, and
agrees with the inclusion induced by any coefficient presentation. -/
theorem native_completed_coefficient_change [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) :
    ∃ a : PurCompactSupport.Change (PurCompactSupport.completed l E) (nativeCoefficients l),
      ∀ (T : Scheme.{u}) (C : CoefficientPresentation l T E i),
        a.map T = C.integralMap l T := by
  obtain ⟨m, C₀, hsquare, hC⟩ := native_completed_coefficient_change_data l E i
  let a : PurCompactSupport.Change (PurCompactSupport.completed l E) (nativeCoefficients l) :=
    { map := m
      square := hsquare }
  refine ⟨a, ?_⟩
  intro T C
  change m T = C.integralMap l T
  rw [hC T]
  exact coefficientPresentation_integralMap_eq l E i T (C₀ T) C

end WeilConjectures.LocallyFiniteAdicCompactSupport
