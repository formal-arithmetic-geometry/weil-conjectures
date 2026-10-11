/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Topology.PresheafModuleStalkFunctor
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Stalks and filtered colimits of presheaves of modules

Source: Stacks Project, Sheaves, Section 009D, item (4)
(blueprint: lem-weil-pbc-presheaf-module-stalk-filtered-colimit).
-/

universe v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Presheaf

/-- The stalk of a sectionwise filtered colimit of presheaves of modules is the
filtered colimit of the stalks as modules over the stalk of the ring presheaf.
Source: Stacks Project, Sheaves, Section 009D, item (4).
(blueprint: lem-weil-pbc-presheaf-module-stalk-filtered-colimit).

Proof outline:
1. Sectionwise colimits have induced restrictions and presheaf-module coprojections
   (`lem-weil-pbc-presheaf-modules-colimits-sectionwise`). Naturality gives
   p_i(t)|_W = p_i(t|_W), and the cocone law gives p_j ∘ D(a) = p_i.
   The induced stalk maps send t_x to p_i(t)_x and preserve identities and composition
   (`def-weil-pbc-module-stalk`). Applying them to the cocone law gives the stalk cocone
   (`def-weil-pbc-category-colimit`).
2. Represent a stalk element by a section on a neighborhood. The sectionwise
   filtered-colimit elementwise description (`lem-weil-pbc-filtered-colimit-modules-elementwise`)
   lifts it to a section at some stage, and hence to a germ at that stage.
3. If a stage germ vanishes in the colimit stalk, shrink its representative's neighborhood
   until its image section vanishes. The same elementwise description gives a later
   stage at which that section vanishes; therefore its germ vanishes there too.
4. Apply the filtered-colimit recognition criterion for modules
   (`lem-weil-pbc-filtered-colimit-modules-criterion`) to these two properties.
-/
theorem isColimit_stalk_mapCocone
    (X : TopCat.{v}) (R : TopCat.Presheaf CommRingCat.{v} X) (x : X)
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
    (c : Cocone D)
    (hc : ∀ (U : TopologicalSpace.Opens X),
      IsColimit ((PresheafOfModules.evaluation
        (R ⋙ forget₂ CommRingCat RingCat) (Opposite.op U)).mapCocone c)) :
    Nonempty (IsColimit ((PresheafOfModules.moduleStalkFunctor
      (R ⋙ forget₂ CommRingCat RingCat) x).mapCocone c)) := by
  sorry

end TopCat.Presheaf
