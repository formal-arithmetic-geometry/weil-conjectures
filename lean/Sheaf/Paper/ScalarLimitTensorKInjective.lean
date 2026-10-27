module

public import Sheaf.Paper.ConstantScalarTowerAdjunction

/-! # K-injective preservation for strict scalar tensor

The finite-free dual-basis argument makes strict scalar extension a right adjoint
of an exact functor, hence it preserves K-injective complexes.
(blueprint: lem-pur-compact-support-scalar-limit-tensor-kinjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Finite-free strict scalar extension preserves K-injective complexes.
Source: Stacks 03CY and 0941; dual-basis tensor/restriction argument.
(blueprint: lem-pur-compact-support-scalar-limit-tensor-kinjective).
Proof: choose an integral basis of the finite free coefficient extension. The
dual basis identifies tensor extension with the corresponding finite coinduction
functor on strict towers. This is right adjoint to an exact finite-coordinate
functor, so the adjunction criterion preserves K-injectives. -/
theorem scalarTensor_preservesKInjective (W : Scheme.{u}) :
    (tensor l E F i W).PreservesKInjectiveComplexes := by
  sorry

end WeilConjectures.PurStrictScalar
