/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.PresheafModuleStalkFilteredColimit
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Filtered colimits and ordinary module stalks

Source: Stacks Project, Sheaves, Section 009E, item (5), and Modules, Lemma 01AH (2)
(blueprint: lem-weil-pbc-module-stalk-filtered-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk maps of a colimit cocone of sheaves of modules exhibit the stalk of the colimit
as the colimit, in modules over the local ring `𝒪_{X,x}`, of the stalks of the diagram. The
stalks and the induced linear stalk maps are those of the module stalk functor
`RingedSpace.moduleStalkFunctor` (`def-weil-pbc-module-stalk`, `def-pc-module-stalk-functor`);
the index category lives in the universe of the modules.
Source: Stacks Project, Sheaves, Section 009E (5), and Modules, Lemma 01AH (2)
(blueprint: lem-weil-pbc-module-stalk-filtered-colimit).

Proof outline:
1. Form the sectionwise colimit P of the underlying presheaves of modules, using
   `lem-weil-pbc-presheaf-modules-colimits-sectionwise` and
   `def-weil-sheaf-of-modules-category`.
2. Sheafification preserves colimits and is the identity on sheaves, so the given colimit
   is isomorphic to P's sheafification compatibly with the coprojections, by
   `def-weil-presheaf-modules-sheafification`,
   `lem-weil-pbc-module-presheaf-sheafification-exact`, and `def-weil-pbc-category-colimit`.
3. The unit of sheafification is an isomorphism on stalks, compatible with the scalar
   actions on germs (`def-weil-pbc-module-stalk` and
   `lem-weil-pbc-stalk-sheafification-space`).
4. The stalk of P is the colimit of the stalks of the presheaves, compatibly with the
   coprojections (`lem-weil-pbc-presheaf-module-stalk-filtered-colimit`).
5. Transport this colimit universal property along the composite isomorphism from P's
   stalk to the given colimit's stalk (`def-weil-pbc-category-colimit`). This shows that the
   image of the cocone under the stalk functor is a colimit cocone, equivalently that the
   canonical map from a chosen colimit of the stalks to the stalk of the given colimit is an
   isomorphism. -/
theorem module_stalk_filtered_colimit
    (X : Scheme.{u}) (x : X) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ X.Modules) (c : Cocone D) (hc : IsColimit c) :
    Nonempty (IsColimit ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapCocone c)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
