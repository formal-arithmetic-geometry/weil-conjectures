/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.NestedSliceExtensionStalks
import WeilConjectures.Topology.ConstantIntegerOpenExtensionComparison

/-! # Inclusion between constant integer extensions on nested opens

## References

* Stacks Project, Tags 0A38 and 00A5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- The nested-open inclusion is the identity on stalks inside the smaller open. -/
theorem abelianIntegerOpen_exists_inclusion
    (X : TopCat.{u}) (U V : Opens X) (hVU : V ≤ U) :
    ∃ f : (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
      (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))),
      ∀ x : X, x ∈ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
  classical
  let C := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  obtain ⟨g, hg⟩ := nested_slice_extension_stalks C U V hVU
  obtain ⟨eV⟩ := TopCat.constant_integer_open_extension_comparison X V
  obtain ⟨eU⟩ := TopCat.constant_integer_open_extension_comparison X U
  let sg := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map g
  refine ⟨eV.hom ≫ sg ≫ eU.inv, ?_⟩
  intro x hx
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (S.map g) := hg x hx
  have : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((siteExtensionByZeroPresheaf V).obj (C.over V).obj))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have : IsIso (S.map (toSheafify (Opens.grothendieckTopology X)
      ((siteExtensionByZeroPresheaf U).obj (C.over U).obj))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have hnat := congrArg (fun f => S.map f)
    (toSheafify_naturality (Opens.grothendieckTopology X) g)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have : IsIso (S.map sg.hom) := by
    have hcomp : IsIso (S.map
        (toSheafify (Opens.grothendieckTopology X)
          ((siteExtensionByZeroPresheaf V).obj (C.over V).obj)) ≫ S.map sg.hom) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left (S.map
      (toSheafify (Opens.grothendieckTopology X)
        ((siteExtensionByZeroPresheaf V).obj (C.over V).obj))) (S.map sg.hom)
  change IsIso (S.map (eV.hom.hom ≫ sg.hom ≫ eU.inv.hom))
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance


end TopCat.Sheaf
