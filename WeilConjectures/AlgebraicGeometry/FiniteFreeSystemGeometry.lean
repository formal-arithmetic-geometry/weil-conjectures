/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeSystemRestrictionData

/-! # Scalar restriction and normalized geometric generators

Source: finite-free restriction proof Steps 6--12; Stacks 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections
namespace WeilConjectures.FiniteFreeSystemRestriction

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

/-- Exact scalar restriction preserves the normalized geometric generators.
Source: lem-coef-finite-free-system-restriction, proof Steps 6--12;
Stacks 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-geometry).

Proof: for each scheme map, ordinary direct image and coefficient restriction
have identical underlying section groups and transition maps. Their identity
comparison is linear and natural. Its inverse adjunct is the inverse-image
comparison, invertible because inverse image commutes with restriction of the
identified constant scalar actions. This constructs OrdinarySquare with its mate
and section equations. ScalarAssertions gives preservation of K-injectives, so
both sides of the derived direct-image comparison are computed on the same
K-injective systems. The derived adjoint-square comparison identifies this
isomorphism with the specified right mate. For an open immersion, extension by
zero is unchanged on the open and zero on its complement. The same identity
comparison is compatible with the open Hom bijection, and exact localization
makes the specified open mate invertible. The coefficient push map is obtained
by restricting the upper constant-section structural map; its pullback adjunct
is invertible since inverse image preserves the constant coefficient sections.
Section identities preserve ordinary direct-image identities and compositors.
Adjunction conjugation and mate pasting preserve the pullback, derived direct-image
and open identities and compositors. The clopen projector is identity on the open
summand and zero on the complementary summand, and restriction preserves both.
The Cartesian open comparison beta is the transpose of its normalized unit and
pullback comparison, so it is preserved. The word defining alpha consists of beta,
this clopen projector and the compositors. Each factor is preserved. Its proper
right mate gamma is the unit--alpha--counit word, hence is preserved by the same
mate-pasting identities. These are equations before evaluation or inverse limit;
no faithfulness of derived evaluation is used. -/
theorem geometryCompatibility_of_scalars (D : FiniteFieldDatum.{u})
    (s : ∀ X : Spaces D, ScalarAssertions l E L i X.val.left) :
    Nonempty {G : Geometry l E L i D // Compatibility l E L i G} := by sorry

end WeilConjectures.FiniteFreeSystemRestriction
