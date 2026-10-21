/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Naturality of finite constant coefficient maps

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-reduction compatibility;
Stacks Project, Tags 00WH and 09A5
(blueprint: lem-cbc-finite-constant-map-naturality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical constant-section map commutes with homomorphisms of finite commutative
coefficient rings, both in inverse-image and adjunct direct-image form.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-reduction compatibility;
Stacks Project, Tags 00WH and 09A5
(blueprint: lem-cbc-finite-constant-map-naturality).

Proof: (1) Pointwise postcomposition with the ring homomorphism preserves constant
sections. Naturality of the sheafification unit gives the same identity on coefficient
sheaves (`def-weil-pbc-proetale-modules`, `def-weil-pbc-sheafification`).
(2) For a continuous function on connected components, use its open fibres. The two
composites send its value on each fibre to the same constant section on the base change;
this uses the construction in `prop-weil-pbc-proetale-constant-ring-map`. Uniqueness of
gluing gives equality on the defining presheaf, including when different fibres merge
under the coefficient homomorphism. The target is a direct-image sheaf, so uniqueness
of extension through sheafification proves the direct-image equality.
(3) Write L for inverse image, R for direct image and epsilon for the counit of the
adjunction in `def-weil-proetale-inverse-image`. By definition c_B = epsilon L(rho_B).
Counit naturality and Step 2 give phi c_B = epsilon L(R(phi) rho_B)
= epsilon L(rho_C phi) = c_C L(phi). Conversely, the adjuncts of the inverse-image
composites are exactly the direct-image composites, by unit naturality. Bijectivity
of the adjunction correspondence identifies the two formulations. -/
theorem finiteConstantMap_naturality
    {T' T : Scheme.{u}} (g : T' ⟶ T)
    {B C : Type (u + 1)} [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] [CommRing C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C] (φ : B →+* C) :
    (finiteCoefficientInverseImageMap g B ≫ finiteScalarRingMap φ T' =
      (Scheme.proEtaleSheafInverseImage g RingCat.{u + 1}).map
        (finiteScalarRingMap φ T) ≫ finiteCoefficientInverseImageMap g C) ∧
    (finiteCoefficientDirectImageMap g B ≫
      (Scheme.proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (finiteScalarRingMap φ T') =
      finiteScalarRingMap φ T ≫ finiteCoefficientDirectImageMap g C) := by
  sorry

end AlgebraicGeometry.ProEtale
