/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow

/-!
# The constructible exceptional unit along a closed immersion

For a closed immersion `i : Z ⟶ X` admitting a compactification, the pro-étale derived lower
shriek `Ri_!` is the right derived pushforward `Ri_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`), hence
fully faithful for pro-étale sheaves of modules. Consequently the unit `Q ⟶ Ri^! Ri_! Q` of the
constructible exceptional adjunction `Hom(Ri_! K, L) ≃ Hom(K, Ri^! L)`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`) is an isomorphism for every
bounded constructible `Q`
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion`):
this is the last assertion of blueprint `prop-sf-closed-immersion-unit`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section LowerShriek

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]

end LowerShriek

section Unit

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i] [HasCompactification i]

end Unit

end ProEtale

end AlgebraicGeometry
