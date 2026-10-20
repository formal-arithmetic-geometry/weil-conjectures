/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality

/-! The upstream sync to slopmaster2 e9ba49ac4 moved
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`
to `SmoothDuality/SmoothBaseChange` and added the hypothesis that the base is quasi-separated.
This module keeps the earlier statement, which was also `sorry` upstream before the sync, under a new name
for the Sheaf modules that use it. It is a stage-3 item. -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `prop-asd-smooth-base-change` without the quasi-separatedness of the base: the
canonical morphism `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism for `f` smooth of relative
dimension `d` and quasi-compact `f'` (the statement of
`isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension` before the sync to e9ba49ac4).
(blueprint: prop-asd-smooth-base-change) -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  sorry

end AlgebraicGeometry.Etale
