/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
public import Sheaf.SixFunctors.OpenScalarTensorData

/-! # Scalar restriction preserves the open adjunction unit

Source: Stacks Project, Tags 03DI, 03CY and 015F; the scalar restriction part of
lem-sp-open-scalar-counit-square, Step 2
(blueprint: lem-sp-open-scalar-restriction-unit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The specified scalar restriction comparison preserves the unit of the open
adjunction after its prescribed constant-pullback coordinate change.
Source: Stacks Tags 03DI, 03CY and 015F; Step 2 of
lem-sp-open-scalar-counit-square (blueprint: lem-sp-open-scalar-restriction-unit).

Proof: sfOpenRestriction_normalized_unique gives the unit equation before deriving,
with right adjoint sfIntrinsicOpenRestriction and coefficient square
sfOpenRestrictionCoefficientSquare. Identify this restriction with intrinsic pullback
by the open upper-star comparison, and then with proEtaleConstantRingPullback by
openSquarePullbackModel. Both comparisons preserve the sectionwise pullback unit.
The coefficient square in these coordinates is the inverse restriction/pullback square:
on sections the two maps carry the same generator to itself, and respect the same
restricted scalar action. This proves the ordinary unit equation in these coordinates.
Apply it in every degree of an arbitrary cochain complex. The exact-localization unit
formula, mapDerivedCategoryNatIso_fac and the exact composition factors identify its
localization with the claimed equation. Finally reductionOpenModel is the localization
of the left-adjoint uniqueness comparison for this very change of right adjoint, so its
unit equation identifies the transported units with the displayed ones. Equality after
precomposition with the localization functor implies equality of natural transformations,
hence the equation holds at every unbounded derived object. No flatness is used. For
an empty open all source objects are zero; for the whole open this is the identity
restriction square; zero complexes satisfy the same unit equation. -/
theorem openScalarRestrictionUnit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ∀ L : proEtaleDerivedCategory X B,
      ((OpenScalarTensor.openAdj A j).ofNatIsoLeft (reductionOpenModel A j).symm).unit.app
          ((scalarRestriction φ X).obj L) ≫
        (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) ≫
        (OpenScalarTensor.rightSquare φ j).inv.app
          ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L) =
      (scalarRestriction φ X).map
        (((OpenScalarTensor.openAdj B j).ofNatIsoLeft (reductionOpenModel B j).symm).unit.app L)
    := by sorry

end AlgebraicGeometry.ProEtale
