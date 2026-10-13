/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Monoidal adjunction for the transported derived pullback

Source: Stacks Project, Tags 079U, 079W and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-monoidal-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- The transported K-flat pullback is strong monoidal and left adjoint to the
specified K-injective direct image, with independent localization universes.
Source: Stacks Project, Tags 079U, 079W and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-monoidal-adjunction).

Proof: Use the canonical monoidal model of derived pullback in the standard
localizations, constructed by deriving the module tensor comparison on K-flat
resolutions. The localization equivalences used in
`derivedPullbackAcrossUniverses` are strong monoidal: compare their tensorators
on K-flat representatives with the fixed derived tensor structures, and descend
associativity and unit coherence by the localization universal property.
Transport the standard pullback monoidal model through these equivalences.
For the adjunction, the module pullback is left adjoint to module direct image.
K-flat pullback and K-injective direct image derive this adjunction (079W).
Uniqueness of the left-derived functor identifies its left side with the
standard `derivedPullback`; uniqueness of the right-derived functor identifies
its right side with `schemeDerivedDirectImage`. Transport unit and counit
through the localization equivalences. The triangle identities are preserved
by equivalence and the right-derived uniqueness isomorphism. This gives an
adjunction whose functors are exactly the two specified functors. No scheme
finiteness condition or perfect argument is used. Only existence of structures
is asserted; no object is defined by choosing an unproved existence witness. -/
theorem exists_derivedPullbackAcrossUniverses_monoidal_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ m : (derivedPullbackAcrossUniverses f).CoreMonoidal,
      Nonempty (derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f) := by sorry

end AlgebraicGeometry
