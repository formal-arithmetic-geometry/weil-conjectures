/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantComplexQuotientModel

/-! # Normalized constant-complex comparisons

Source: Stacks Project, Modules on Sites, Tags 03EK, 03EL and 03CZ.
(blueprint: lem-a1-constant-complex-normalized-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] AlgebraicGeometry.Scheme.coefficientProEtaleModelBaseChange_isContinuous
  WeilConjectures.integralOperationsSiteSmall WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
open scoped ChangeOfRings
namespace AlgebraicGeometry.ConstantComplexBaseChange

/-- Compatible quotient reductions of a constant complex on one site.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03CZ.
(blueprint: lem-a1-constant-complex-normalized-reductions).

Proof: The constant quotient maps form a cone, so define the coefficient map by its
limit lift. Sheafify the balanced maps `a ⊗ m ↦ q(a) ⊗ m` to obtain the finite
transitions and their scalar restrictions. Tensor associativity identifies reduction
of the completed complex with the finite complex, sending `a ⊗ (b ⊗ p)` to
`a * pr(b) ⊗ p`; its inverse inserts the coefficient unit. The scalar adjunction unit
is `m ↦ 1 ⊗ m`. Define alpha as this unit followed by the restricted associativity
map. All transformations are natural before passage to complexes. The projection
identity `pr(n+1) ≫ q = pr(n)` proves the reduction square by the two tensor
universal properties, hence its unit square and alpha compatibility. Applying the
additive functors termwise preserves every differential and scalar chain map.
These constructions also cover the zero ring, zero complex and empty scheme. -/
theorem normalized_reductions_exist (W : Scheme.{u}) {R : Type u} [CommRing R]
    (I : Ideal R) :
    ∃ (d : FiniteTower W I) (e : ReductionData W I d),
      d.IsNormalized W I ∧ e.IsNormalized W I := by sorry

end AlgebraicGeometry.ConstantComplexBaseChange
