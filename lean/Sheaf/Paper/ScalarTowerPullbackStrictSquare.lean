/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ScalarExtensionTowerRealizationData

/-! # Strict scalar/pullback square below the total-limit comparison

Source: Stacks 03EL and 07A4; strict part of
lem-pur-scalar-extension-tower-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Equality of normalized scalar/pullback maps before localization and total limit.
The proof is the homogeneous generator calculation: both routes send a generator
`b ⊗ (x ⊗ y)` to `(b ⊗ x) ⊗ (1 ⊗ y)`, and the equality is retained by every
quotient transition.  This is strictly below the target's realization and limit
statement.
Source: Stacks 03EL and 07A4
(blueprint: stage3-pur-scalar-pullback-strict-square).
Proof: compare homogeneous generators after applying the scalar adjunction
transpose; the scalar and pullback formulas agree and preserve every quotient
transition.
-/
theorem scalarTowerPullbackStrictSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftRoute l E L ι f = rightRoute l E L ι f := by
  sorry

end WeilConjectures.ScalarExtensionTower
