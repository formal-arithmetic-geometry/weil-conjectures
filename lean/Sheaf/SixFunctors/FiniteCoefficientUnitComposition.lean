/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Sheaf.Paper.WitnessCompatibility

/-! # Composition of normalized regular scalar units

Source: lem-coef-integral-finite-extension.proof.md, quotient compatibility;
lem-coef-finite-dualizing.proof.md, the coefficient counit cocycle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory

namespace WeilConjectures

/-- The regular scalar-unit identifications compose with the associator obtained
from restriction of scalars. This is a coefficient-only statement, with no compact
support functor, exceptional adjoint, dualizing object or realization functor.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, quotient compatibility in paragraphs 2--3;
lem-coef-finite-dualizing.proof.md, the coefficient counit cocycle.
(blueprint: lem-sf-finite-coefficient-unit-composition)

Proof: the ordinary scalar-unit comparisons are multiplication maps on the regular
module. Their restriction adjuncts send the regular generator to 1. The successive
adjuncts therefore compose to the adjunct for the composite coefficient homomorphism,
as is checked by the constant-sheaf adjunction on that generator. Apply the exact
restriction functors to complexes and localize. The scalar associator is the
left-adjoint conjugate of the resulting restriction-composition isomorphism.
The normalized derived unit comparisons agree with these localized ordinary
adjuncts: their representative equation is precisely UnitNormalization, whose
solution is unique. Transposing the ordinary generator equation thus gives the
displayed equation. This uses no flatness of either coefficient homomorphism;
the regular unit itself is K-flat. Identity maps and the zero ring obey the same
multiplication equations. -/
theorem finiteCoefficient_unit_composition
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (S : Scheme.{u}) :
    (Etale.scalarExtension ψ S).map (Etale.ExceptionalCoefficients.unitIso φ S).hom ≫
        (Etale.ExceptionalCoefficients.unitIso ψ S).hom =
      (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ hχ).hom.app
          (𝟙_ (Etale.DerivedCategoryModule A S)) ≫
        (Etale.ExceptionalCoefficients.unitIso χ S).hom := by sorry

end WeilConjectures
