/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData

/-!
# Compatibility of finite open normalization comparisons

This is the mate-identification part of the finite specialization.
(blueprint: lem-sf-finite-compatibility-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The pinned finite comparisons transport the published base-change and
projection arrows to the normalized arrows.

Proof: conjugate the inverse of the published finite base-change isomorphism
by the pullback and shriek comparisons. Apply the derived open adjunction to
this arrow. On an exact complex representative, the pull pins' mate equations
and the open pins' unit equations identify its transpose with the pullback of
the open unit followed by the inverse theta comparison. To check the square
used here, apply the underlying-sheaf comparisons: right_sections and the
open section equations identify it with the fixed sectionwise right square
in Operations. This is precisely the right-adjoint comparison whose conjugate
defines ordinaryOpenExtensionBaseChangeIso. The comparison on derived flat
representatives is the same one by the pull and open model equations and
Operations.theta_model. Localization therefore gives the same transpose as
a.beta_inverse. Injectivity of the open adjunction Hom equivalence
identifies the inverse arrows. Cancel the isomorphisms to obtain the forward
route equality finiteBetaLeft = finiteBetaRight.

For projection, conjugate the inverse of the finiteGamma arrow by the tensor,
shriek and open-pull comparisons. The published finite projection map is the
open-adjunction transpose of the tensor of the open unit with the identity.
The ordinary open pin's unit equation identifies the units under realization.
On a flat K-flat pair of complexes, the tensor pins' pure-summand equations
identify both tensors on every bidegree generator with the same pure tensor;
the restriction-tensor pure equation in Operations identifies restriction of
this map. The equality extends from pure tensors to the sheafified tensors
by their universal property and to the signed total complexes by their coproduct
universal property. Naturality makes it an equality of chain maps, with the
same sign on the second differential. The tensor model equations and the open
model equations descend this equality to the derived tensor functors, giving
exactly the transpose in a.gamma_inverse. Injectivity of the adjunction
Hom equivalence identifies the inverse maps; cancellation gives
finiteGammaLeft = finiteGammaRight. These are the two conjuncts of
FiniteCompatibility. Neither argument chooses a beta or gamma comparison.

Source: Stacks 03S6 and 0GL1; the defining conjugate in
ProEtaleDerivedExtensionZeroBaseChange and the canonical projection map in
OpenLowerShriekProj fix the orientations used above.
(blueprint: lem-sf-finite-compatibility-transport) -/
theorem finite_compatibility_of_comparisons (A : Type (u + 1)) [CommRing A]
    [Finite A] {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) (a : Assertion o)
    (e : FiniteComparisons A o) : FiniteCompatibility A o a e := by
  sorry

end SheafOfModules.OpenTensorNormalization
