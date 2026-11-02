/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarTensorData

/-! The constant coefficient model respects canonical pullback.
Source: Zheng Construction 2.26; Stacks 07A4 and 07A6
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The two canonical ways to pull back the restricted coefficient module agree.
Source: Zheng Construction 2.26; Stacks 07A4 and 07A6
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback).

Proof: first work with sheaves. The restriction/pullback isomorphism is the unique
comparison of the two composites left adjoint to direct image followed by coextension.
The constant-sheaf comparison with restriction preserves the constant adjunction counit.
Apply the two composite adjunction Hom equivalences to the claimed square on the free
rank-one B-module. Both transposes are the sectionwise identity, so injectivity gives
the square. The monoidal unit comparison is its value on the free rank-one module:
its transpose is the lax direct-image unit, hence the same sectionwise identity.
Now apply the degree-zero single functor. Naturality of the exact derived/single
comparison and the composition comparison identifies the resulting square with the
one displayed here. Cancel the exact derived/single isomorphisms; this gives the
claimed equality with the actual chosen comparisons, including their units. -/
theorem ordinaryExceptional_scalarCoefficient_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        (ordinaryScalarCoefficientIso φ Y).hom ≫
      ((constantFunctorCompLeftDerivedUpperStarIso A p).app
        (ordinaryCoefficientComplex φ)).hom =
      (scalarCoefficientPullbackIso φ p).hom ≫ (ordinaryScalarCoefficientIso φ Z).hom := by
  sorry

end AlgebraicGeometry.Etale
