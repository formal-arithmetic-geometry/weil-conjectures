/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Brown adjoints for proper finite-coefficient direct image

Source: Stacks Project, Tag 0F5Y; the finite-level step in the proof of
`lem-sfb-dc-proper-pushforward-left-adjoint-oe`.
(blueprint: lem-sfb-finite-proper-brown-adjoint)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The ordinary unbounded derived proper direct image with finite coefficients
has a right adjoint over an arbitrary base scheme.

Source: Stacks Project, Tag 0F5Y, and the finite-level step in the proof of
`lem-sfb-dc-proper-pushforward-left-adjoint-oe`.
(blueprint: lem-sfb-finite-proper-brown-adjoint)

Proof: finite rings are additive torsion, so proper derived direct image
preserves every coproduct. The derived pullback/direct-image adjunction equips
it with a shift commutation and a triangulated structure. The category of
module sheaves is Grothendieck abelian. Brown representability for its ordinary
unbounded derived category therefore supplies the right adjoint. This includes
empty schemes and the zero coefficient ring, and needs no absolute
cohomological-dimension bound on a field.
-/
theorem finite_proper_brown_adjoint
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] :
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.IsLeftAdjoint := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  let : (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor :=
    preservesColimitsOfShape_rightDerivedLowerStar_of_isProper A isAddTorsion_of_finite p I
  exact DerivedCategory.isLeftAdjoint_of_preservesCoproducts _

end AlgebraicGeometry.Etale
