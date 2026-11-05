/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyColimitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionsWithSupportHomology

/-!
# Continuity of `Hom` out of a closed pushforward

Let `Λ` be a commutative condensed ring with `Λ_X` flat, `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`. If `Hom(s, -[q])` commutes with filtered colimits of module
objects over `Λ_Z` and `s` is bounded above, then so does `Hom(Ri_* s, -[q])` over `Λ_X`
(`homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion`, blueprint
`sk-lem-constructible-ext-continuity`, closed-support step via
`sk-lem-formal-closed-support`).

Indeed `Hom(i_* s, B[q]) = Hom(s, (Ri^! B)[q])`
(`ProEtale.CondensedRing.derivedLowerStarClosedUpperShriekAdjunction`),
`Ri^! B = i^* RΓ_Z B` is concentrated in degrees `≥ 0`, and its cohomology commutes with filtered
colimits: `RΓ_Z B` sits in the natural triangle `RΓ_Z B ⟶ B ⟶ Rj_* j^* B ⟶`, whose last two terms
have this property
(`sk-cor-pe-bounded-continuity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

end AlgebraicGeometry.ProEtale.CondensedRing
