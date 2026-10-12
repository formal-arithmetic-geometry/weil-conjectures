/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Shift compatibility of the bounded below derived étale adjunction

Source: Stacks Project, Derived Categories, Tags 0A8D, 0DVC and 05SU;
(blueprint: lem-weil-pbc-derived-adjunction-commshift).

The shift structures are the existing termwise structure on `mapDerivedCategoryPlus` and
resolution-comparison structure on `rightDerivedFunctorPlus`, not structures transported
from an abstract adjunction. `Adjunction.CommShift ℤ` asserts compatibility of both the
unit and counit, including all iterated integer shifts.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The unit and counit of `u⁻¹ ⊣ Ru_*` on bounded below derived categories of abelian
étale sheaves commute with the specified shift isomorphisms, for every integer shift.
Source: Stacks Project, Tags 0A8D, 0DVC and 05SU;
(blueprint: lem-weil-pbc-derived-adjunction-commshift).

Proof plan from the node:
1. Compare K-injective resolutions using the unique homotopy classes of comparisons
   (`lem-weil-pbc-kinjective-hom-derived`). Shifting a resolution remains a resolution
   (`lem-weil-pbc-kinjective-shift`). The comparison shift isomorphism on a K-injective
   representative is the termwise identity, after the resolution identifications.
2. Compute the counit on a K-injective representative by the termwise sheaf counit
   (`prop-weil-pbc-derived-inverse-image-adjunction`). Its components commute with shift;
   combine with step 1 and naturality of the inverse-image shift isomorphism.
3. Transport the counit equality along a K-injective representative isomorphism by
   naturality (`lem-weil-pbc-dplus-injective-representative`).
4. Compute the unit on a bounded below complex by the termwise unit followed by the
   direct image of its inverse-image resolution. Shift the resolution and use uniqueness
   of comparisons to obtain the unit equality.
5. Transport the unit equality to every derived object using a bounded below
   representative and naturality (`lem-weil-pbc-dplus-injective-representative`).
6. The composite shift structures are the whiskered composites
   (`lem-weil-pbc-triangulated-functor-composite`,
   `lem-weil-pbc-commshift-nattrans-comp-whisker`). Induct for positive shifts, use inverses
   for negative shifts, and use the identity for zero.
7. The unit equality identifies the resolution-comparison structure with the unique
   adjunction-induced structure (`lem-weil-pbc-adjunction-shift-compatibility-unique`). -/
theorem derivedPlus_upperStarLowerStar_commShift {U V : Scheme.{u}} (f : U ⟶ V) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus).CommShift ℤ := by
  sorry

end AlgebraicGeometry.Etale
