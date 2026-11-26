/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import Mathlib.Topology.Sheaves.Abelian

/-! # Cohomology of the empty space

## References

* Stacks Project, Tag 02UZ.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Every abelian sheaf on the empty space has zero cohomology in every degree. -/
theorem cohomology_vanishing_of_isEmpty
    (X : Type u) [TopologicalSpace X] [IsEmpty X] (q : ℕ)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (CategoryTheory.Sheaf.H' F q (⊤ : Opens X)) := by
  have hF : IsZero F :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (X := TopCat.of X) F).mpr
      (fun x ↦ isEmptyElim x)
  exact Functor.map_isZero (CategoryTheory.Abelian.extFunctorObj _ q) hF

end TopCat
