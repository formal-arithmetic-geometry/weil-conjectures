/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.RingedExtendedCech

import Sheaf.Algebra.Homology.TelescopeColimit

/-! The augmentation-compatible colimit identification for the ringed Koszul system.
Source: Stacks Project, More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-cech-koszul-colimit-iso).
(blueprint: lem-weil-pbc-ringed-cech-koszul-colimit-iso)
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- The colimit of the positive ringed Koszul system is the extended Cech complex,
compatibly with the augmentation.  The proof expands subset summands, identifies the
filtered colimit of each transition-by-product system with sectionwise localization,
and then inducts over the ordered tensor factors.
(blueprint: lem-weil-pbc-ringed-cech-koszul-colimit-iso).
Proof: expand the finite subset summands and identify each transition-by-product filtered colimit
with sectionwise localization, then induct over the ordered tensor factors. -/
theorem exists_ringed_cech_koszul_colimit_iso :
    ∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) := by
  sorry

end CategoryTheory
