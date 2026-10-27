module

public import Sheaf.Paper.ConstantComplexStrictBaseChangeData

/-! # Normalized constant-complex comparisons

Source: Stacks Project, Modules on Sites, Tags 03EK, 03EL and 03CZ.
(blueprint: lem-a1-constant-complex-completed-pullback).
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

/-- Completed coefficient pullback commutes with the normalized finite reductions.
Source: Stacks Project, Modules on Sites, Tags 03EL, 03EK and 03CZ.
(blueprint: lem-a1-constant-complex-completed-pullback).

Proof: Compose inverse images of the source limit projections with the canonical
constant-ring comparisons. Naturality in the quotient maps makes these a cone;
its limit lift defines c, with the required projection equations. Compare the
completed constant complexes by scalar associativity and the constant-module
inverse-image comparison: `b' ⊗ inverse(b ⊗ p)` maps to `b' * c(unit b) ⊗ p`.
The inverse inserts the scalar unit and the inverse constant-module comparison;
balancing proves both composites are identities. This is natural in the original
scalar differential and every scalar chain map. Pull alpha through the scalar
restriction/pullback comparison and extend scalars along c. Its local formula is
`pr(b')` times the pulled section alpha(m). The projection equations for c identify
the two composites of the reduction square on tensor generators. Sheaf tensor
universality extends the equality to all sections. No inverse to c is required;
the argument applies also to the zero ring and empty schemes. -/
theorem normalized_completed_pullback_exists {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Type u} [CommRing R] (I : Ideal R)
    {dY : FiniteTower Y I} {dX : FiniteTower X I}
    (eY : ReductionData Y I dY) (eX : ReductionData X I dX)
    (heY : eY.IsNormalized Y I) (heX : eX.IsNormalized X I)
    (f : FiniteComparison g I dY dX) (hf : f.IsNormalized g I) :
    ∃ e : GeometricReduction g I eY eX f, e.IsNormalized g I := by sorry

end AlgebraicGeometry.ConstantComplexBaseChange
