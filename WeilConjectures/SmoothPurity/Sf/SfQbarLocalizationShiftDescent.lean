/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.Functor

import all WeilConjectures.SmoothPurity.Sf.SfFrameworkCommonStageDescent

/-! # Shift descent on the general rational coefficient stages

Coherent finite shift comparisons of a family of coefficient-stage functors induce a shift
comparison of the pair functor on the general rational coefficient stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Coherent finite shift comparisons induce a shift comparison of the pair functor. -/
theorem sfLocalizationShiftDescent {V W : Scheme.{u}}
    (F : (stageSystem l Ω V).Morphism (stageSystem l Ω W))
    (c : ∀ E, (F.Φ E).CommShift ℤ)
    (hc : ∀ {E L : Index l Ω} (h : E ≤ L),
      let := c E
      let := c L
      NatTrans.CommShift (F.β h).hom ℤ) :
    ∃ s : F.functor.CommShift ℤ,
      letI := s
      ∀ E : Index l Ω,
        let := c E
        NatTrans.CommShift (F.ιCompFunctorIso E).hom ℤ := by
  let := c
  exact ⟨pairCommShift F (fun {_ _} h ↦ hc h),
    fun E ↦ pairRestrictionShift F (fun {_ _} h ↦ hc h) E⟩

end WeilConjectures
