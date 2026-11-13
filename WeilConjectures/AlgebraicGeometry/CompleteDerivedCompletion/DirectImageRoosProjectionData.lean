/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! Canonical derived-limit projection normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The canonical counit projections form the first map of the Milnor triangle.
Source: Stacks Tags 0940 and 0941. -/
theorem directImage_roos_projection_data (T : Scheme.{u}) :
    ∃ (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : DTow l E T,
        ∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E T n).app M) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E T n).app M) δ := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
