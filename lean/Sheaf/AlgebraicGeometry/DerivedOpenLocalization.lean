module

public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact

/-! # Derived localizations on opens in the ambient Hom universe

Source: Stacks Project, Tag 08BT, and Mathlib's HasDerivedCategory convention.
(blueprint: lem-pc-derived-open-localization-universe).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- An ambient derived localization with Hom universe w supplies such localizations on
all opens. This is a size statement, not a new hypothesis on the scheme.
Source: Stacks Project, Tag 08BT (exact extension-by-zero/restriction adjunction),
and Mathlib.Algebra.Homology.DerivedCategory.Basic, HasDerivedCategory.standard.
(blueprint: lem-pc-derived-open-localization-universe).

Proof: Fix U and initially form the standard derived category of modules on U, without
requiring its Hom universe to be w. Extension by zero and restriction are exact and
adjoint by lem-sc-derived-open-restriction-adjunction-exact, so they induce an adjunction
on the standard derived categories (Tag 08BT). Restricting extension by zero back to U
is naturally the identity, checked on stalks: inside U the stalk is unchanged. Thus the
unit is an isomorphism, and derived extension by zero is fully faithful. The ambient
standard derived category is equivalent to the chosen ambient localization by the
universal property of localization. Consequently each Hom in the standard derived
category on U is in bijection with a Hom of the chosen ambient localization and is
w-small. Replace these Hom types by their w-small models, transport identities and
composition along the bijections, and compose the standard localization functor with
this equivalence. The resulting category and functor give HasDerivedCategory in universe
w for modules on U. Choose this construction for every open U; choice gives the stated
nonempty dependent family. Empty and total opens work by the same adjunction; neither
quasi-compactness nor quasi-separatedness is needed. -/
theorem nonempty_derivedOpenLocalization (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) := by
  sorry

end AlgebraicGeometry
