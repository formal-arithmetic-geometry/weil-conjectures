/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportStrictScalarMate

/-! # Scalar compatibility with the normalized strict pullback compositor

Source: Stacks Project, Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 3--6 and 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] T U scalarAdj properRestriction openTensor strictScalarPull
  AlgebraicGeometry.ProEtale.StrictTower.G AlgebraicGeometry.ProEtale.StrictTower.J
  AlgebraicGeometry.ProEtale.StrictTower.R

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The inverse scalar/pullback identifications respect the specified pullback compositor.
Source: Stacks Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 3--4.
(blueprint: lem-pur-strict-scalar-pull-composition).
Proof: restriction of coefficients commutes with two successive ordinary direct images:
all three comparison maps act as the identity on the same sections over the iterated
base change. The module direct-image compositor identifies these sections with those
over the composite. Derive this square using the whole-complex resolution units that
uniquely specify properRestriction. Take its conjugate under the composite geometric
and scalar adjunctions. Conjugation preserves composition and the ordered units and
counits. The resulting left-adjoint comparisons are precisely strictScalarPull;
the geometric pullback compositor is gComp. This gives the displayed equation on
strict tower derived categories, including the prescribed transition maps. -/
theorem strictScalarPullComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom.app
        ((T l E F i Z).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).inv.app M) ≫
        (strictScalarPull l E F i f).inv.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj M) =
      (strictScalarPull l E F i (f ≫ g)).inv.app M ≫
        (T l E F i X).map
          ((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom.app M)
    := by sorry

end WeilConjectures.PurStrictScalar
