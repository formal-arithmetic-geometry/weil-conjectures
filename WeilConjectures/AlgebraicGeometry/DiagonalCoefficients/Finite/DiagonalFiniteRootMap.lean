/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement

/-! # The finite root comparison with its actual kernel inclusion
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The finite root comparison is the kernel-normalized Cartier comparison.
It is available at every positive invertible exponent, without a root generator. -/
theorem diagonalFiniteRoots_exists (X : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hX : IsUnit (N : Γ(X, ⊤))) : Nonempty (FiniteRoots X N) := by
  refine ⟨⟨cartierRootsIso X N hN hX, ?_⟩⟩
  change cartierRootsComparison X N ≫ kernel.ι (Scheme.proEtaleUnitsPower X N) = _
  unfold cartierRootsComparison
  exact kernel.lift_ι _ _ _

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
