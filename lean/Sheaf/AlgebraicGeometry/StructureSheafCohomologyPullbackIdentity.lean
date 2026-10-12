/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback

/-! Identity law for pullback on structure-sheaf cohomology.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-identity)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical pullback along an identity scheme morphism is the identity.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial
and Remark 01FB.

Proof: Write L for inverse image along the identity and let alpha : L ≅ Id
be the unique left-adjoint comparison with identity direct image, compatible with the
adjunction unit. The adjoint of the identity structure map is alpha at the additive
structure sheaf O. Write c : Z ≅ L(Z) for the constant-integer-sheaf comparison used
in the definition. Its construction by uniqueness of left adjoints gives
c.hom ≫ alpha.hom.app Z = id. Naturality of alpha on the derived category identifies
L(x) followed by alpha at O with alpha at Z followed by x, for every Ext class
x : Ext Z O n. Unfolding H.mapFunctor and H.map, pullback sends x to the Yoneda
composite c.hom ; L(x) ; alpha at O. Substitution and cancellation give x.
Thus the additive homomorphism is the identity in every degree. In degree zero this
is the usual identity map on global sections; the argument also applies to the empty
scheme, where all the cohomology groups are zero.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-identity) -/
theorem structureSheafCohomologyPullback_identity (X : Scheme.{u}) (n : ℕ) :
    structureSheafCohomologyPullback (𝟙 X) n =
      AddMonoidHom.id (Sheaf.H (structureSheafAb X) n) := by
  sorry

end AlgebraicGeometry.Scheme
