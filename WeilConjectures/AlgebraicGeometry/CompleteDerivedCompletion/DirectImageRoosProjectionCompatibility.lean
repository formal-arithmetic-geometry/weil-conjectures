/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData

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
/-- The conjugate limit comparison preserves the canonical counit projections.
Source: Stacks Tag 0A07. -/
theorem directImage_roos_projection_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DTow l E X) (n : ℕ) :
    (pushLimitIso l E f).hom.app M ≫
        (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
        (pushEvaluationMap l E f n).app M =
      (rpushModule l E f).map ((levelProjection l E X n).app M) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
