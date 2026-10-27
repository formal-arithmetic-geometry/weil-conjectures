/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CompletedPullbackReductionData

/-! Split result for the finite reduction of completed pullback.
(blueprint: lemma-weil-pbc-completed-pullback-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- Every projection-induced arrow in the completed reduction tower is invertible.

Source: Stacks Tag 099N (5), completed-pullback reduction, finite projection clause
(blueprint: lem-weil-pbc-completed-pullback-reduction-arrow-isIso).

Proof: restrict the completed coefficients to the constant coefficient ring.
The augmented strict-tower comparison identifies the defining pulled tower with
ordinary pullback followed by its quotient tower. It preserves the augmentation
and each finite projection. The constant/completed coefficient equivalence
identifies the derived limit with intrinsic Koszul completion. The completion
reflector and nilpotence of the ideal on every finite quotient show that reduction
of its unit is invertible: the reflector gives bijections on maps to restricted
finite objects, and the scalar adjunction and coyoneda detect this isomorphism.
Under the normalized finite pullback comparison, the projection-induced arrow
composed with the reduced completion unit is the identity: the adjuncts of both
composites are the finite quotient unit, since the limit projection composed with
the augmentation is the finite quotient unit. Thus the arrow is the inverse of
an isomorphism. Exact scalar restriction reflects isomorphisms, giving the claim
with its finite coefficient action. No coherence clause is needed. The argument
allows the zero ring, empty scheme, and empty generating tuple. -/
theorem completedPullbackReductionArrow_isIso
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    ∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n) := by
  sorry

end AlgebraicGeometry.Scheme
