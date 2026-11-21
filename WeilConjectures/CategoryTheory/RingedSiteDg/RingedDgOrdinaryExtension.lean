/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules

/-! The ordinary tensor/restriction construction is the first scalar step.

## References

* Stacks Project, `sdga.tex` (dg bimodules).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The balanced sheaf tensor represents ordinary scalar extension, with the
unit inserting one and counit given by the module action.
Stacks Project, `sdga.tex`. -/
theorem ordinary_extension_exists
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Nonempty (OrdinaryExtension φ) := by
  sorry

end CategoryTheory.RingedSiteDg
