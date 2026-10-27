/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.ScalarSixCtfGenerators
public import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-! # Thickness of bounded constant-model constructible complexes for admissible rings.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-admissible-thickness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Thickness of bounded constant-model constructible complexes for admissible rings.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-admissible-thickness).

Proof in words: use the coefficient isomorphism from admissibility to reduce to a
native coefficient. In the finite case the normalized finite discrete equivalence
identifies bounded constant-model constructibility with the ordinary finite-ring
notion; proEtale_bounded_constructible_isTriangulated supplies triangles and shifts.
A retract has cohomology the kernel of its complementary idempotent; descend this
idempotent to the etale constructible heart and use its kernel closure, as in
finiteCtfRetractEtaleImages (the argument for constructibility uses only boundedness).
For integral coefficients integralConstantModelHeart gives triangulation and ambient
kernel closure; a cohomological retract is the kernel of one minus its idempotent,
so it remains constructible. For fields coefficientHeartTriangulated gives all three
properties directly. Vanishing outside a bounded interval is inherited by retracts
in all cases. The coefficient-isomorphism equivalence preserves cohomology, shifts,
triangles and the same finite constant models, hence transports these conclusions.
Zero coefficients and the empty scheme give the zero category and satisfy them too. -/
theorem sfbAdmissibleConstructibleThickness (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (constantModelBoundedConstructible Λ.X X.left).IsTriangulated ∧
      (constantModelBoundedConstructible Λ.X X.left).IsStableUnderRetracts := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
