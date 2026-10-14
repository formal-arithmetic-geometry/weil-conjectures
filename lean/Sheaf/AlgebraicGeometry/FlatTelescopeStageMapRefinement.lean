/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Refining a homotopy map to maps of flat towers

Source: the common-replacement argument in step 3 of the normalized telescope
comparison plan, Stacks Project Tags 06YS, 06YJ and 04VC.
(blueprint: lem-sc-flat-telescope-stage-map-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A homotopy map between telescope representatives admits a common source
on which it is induced by maps of bounded-flat towers. This assertion contains
no pullback, tensorator, or normalized comparison.

Source: Stacks Project, Tags 06YS and 06YJ, common flat replacement, and Tag 04VC,
right fractions; this explicit tower refinement is the expansion of parent
step 3 rather than a literal assertion of those tags.

Proof. Choose flat-tower presentations of the two objects, with their given
possible one-fold translates. Lift the homotopy morphism to a cochain map.
Resolve the resulting arrow diagram by bounded-above flat truncation towers,
retaining the maps to both original diagrams. At a given truncation level use
a common flat resolution for the source and the pullback of the target
resolution along the arrow; the projections then give a commuting square.
Construct the next level resolving this square together with the previous
level, so the transition squares commute. Taking sums and their transition
cones gives a third flat telescope R and two model maps a and b. The source
augmentation is a quasi-isomorphism by the flat truncation telescope comparison.
Their composites represent the given arrow after localization. Apply the right
fraction equality criterion and refine the source once more to turn that
localized equality into equality in the homotopy category. Compose the two
source refinements; their quasi-isomorphisms compose, and the composite tower
maps are again tower maps. Shift the diagrams and transport by their original
homotopy isomorphisms to cover the translated presentations. Thus a;s=b in the
homotopy category, with a a quasi-isomorphism. For the zero map use the zero
arrow diagram; for the identity use its identical presentations. Empty schemes
have the unique zero diagrams, so no nonzero-object assumption is needed.
(blueprint: lem-sc-flat-telescope-stage-map-refinement). -/
theorem exists_flat_telescope_stage_map_refinement (Y : Scheme.{u})
    {X X' : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (hX : flatTelescopeShiftRepresentative Y X)
    (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X') :
    ∃ (R : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (a : R ⟶ X) (b : R ⟶ X'),
      flatTelescopeShiftRepresentative Y R ∧
        HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) a ∧
        flatTelescopeStageMap Y a ∧ flatTelescopeStageMap Y b ∧ a ≫ s = b := by sorry

end AlgebraicGeometry
