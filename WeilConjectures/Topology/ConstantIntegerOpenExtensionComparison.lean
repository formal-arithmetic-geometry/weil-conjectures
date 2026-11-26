/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.AbelianOpenExtensionByZero
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Sheaves.Over
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Comparing constant integer open extensions

## References

* Stacks Project, Tag 02UZ.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- The extension by zero of the constant integer sheaf on an open `U` is isomorphic to the
sheafified slice-site extension by zero of the constant integer sheaf on `X` restricted to `U`.
-/
theorem constant_integer_open_extension_comparison (X : TopCat.{u}) (U : Opens X) :
    Nonempty
      (((TopCat.Sheaf.abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          ((siteExtensionByZeroPresheaf U).obj
            (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
              (AddCommGrpCat.of (ULift.{u} ℤ))).over U).obj)) := by
  let J := (Opens.grothendieckTopology X).over U
  let K := Opens.grothendieckTopology ↥U
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  let e := (equivCommuteConstant' J AddCommGrpCat.{u} K U.overEquivalence.functor
    Over.mkIdTerminal (by
      convert (isTerminalTop : IsTerminal (⊤ : Opens ↥U)) using 1
      ext x
      exact iff_of_true x.property True.intro)).app M
  let r := ((Opens.grothendieckTopology X).overPullbackConstantSheafIso
    AddCommGrpCat.{u} U).app M
  exact ⟨(presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
    ((siteExtensionByZeroPresheaf U).mapIso
      ((sheafToPresheaf J AddCommGrpCat.{u}).mapIso (e.symm ≪≫ r.symm)))⟩

end TopCat
