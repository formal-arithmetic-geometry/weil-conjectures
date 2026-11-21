/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.SheafDgHomotopySystem

/-! The homotopy-system and localization steps produce a standard derived
structure for each coefficient algebra.

## References

* Stacks Project, `sdga.tex`, Tags 0FS7, 0FT4 and 0FT5.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Localize the supplied homotopy system and transport its standard shift and
cone characterization to the fixed localization of actual modules.
Source: Stacks sdga, 0FT5 and derived, 05R6. -/
theorem derived_structure_from_homotopy_system
    (O : Sheaf J CommRingCat.{u}) (A : Algebra.{c, v, u} O) (hs : HomotopySystem A) :
    Nonempty (DerivedStructure A) := by
  sorry

end CategoryTheory.RingedSiteDg
