/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# The unit of `t^* ⊣ Rt_*` at complexes with constant cohomology over a strictly henselian ring

Let `R` be a strictly henselian local ring, `Y = Spec R` with closed point
`s₀ : Spec κ ⟶ Y` and `t : Spec Ω ⟶ Y` a morphism from the spectrum of a separably closed field.
For a bounded below complex `G` of étale sheaves of `Λ`-modules on `Y` all of whose cohomology
sheaves are constant, the pullback to the closed point of the unit `G ⟶ Rt_* t^* G` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_app_of_isConstant_homology`).
This is the case of a single constant sheaf
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing`)
extended by dévissage along the truncation triangles
(`DerivedCategory.Plus.isIso_app_of_forall_homology`); both `s₀^*` and `s₀^* Rt_* t^*` are left
`t`-exact.

Moreover every bounded below complex on `Spec Ω` is the pullback of such a complex on `Y`
(`AlgebraicGeometry.Etale.exists_isConstant_homology_iso_upperStar_obj`): sheaves on the
separably closed point are constant (`constantSheafEquivalenceOfIsSepClosed`), and pullbacks of
constant sheaves are constant (`AlgebraicGeometry.Etale.constantSheafCompUpperStarIso`). The
property of having constant cohomology sheaves is stable under pullback
(`AlgebraicGeometry.Etale.isConstant_homology_upperStar_obj`).

In the language of nearby cycles: for a strictly henselian trait `Y` with geometric generic point
`t`, the nearby cycles `s₀^* Rt_*` of the constant complex `t^* G` are `s₀^* G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry
