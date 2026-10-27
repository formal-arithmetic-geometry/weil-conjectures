module

public import Sheaf.Paper.NativeConstantSupportModel

/-! # K-injective preservation for constant scalar restriction

Restriction from completed to constant coefficients is the exact right adjoint
of finite-free completed scalar extension.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-kinjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict tower restriction to constant scalars preserves K-injectives.
Source: Stacks 03DA and 0940; exact scalar restriction adjunction.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-kinjective).
Proof: the constant restriction functor is the right adjoint of completed
scalar extension. Exactness of the extension follows from finite-free scalar
coordinates, and whiskering the adjunction over the tower index preserves
K-injective complexes by the exact-adjunction criterion. -/
theorem scalarRestriction_preservesKInjective (W : Scheme.{u}) :
    (towerConstantRestriction l E W).PreservesKInjectiveComplexes := by
  sorry

end WeilConjectures.PurStrictScalar
