/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit

/-! # Forgetting constant scalars commutes with inverse image

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The constant-scalar forgetful functor commutes with inverse image. -/
theorem diagonalRlimForgetPullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⋙ diagonalForget l X ≅
      diagonalForget l S ⋙ upperStar AddCommGrpCat.{u + 1} f) := by
  exact ⟨forgetPullbackIso l f⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
