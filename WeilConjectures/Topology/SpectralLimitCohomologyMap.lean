/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB

/-! # Canonical cohomology map of a topological f-map

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 0A37.
(blueprint: def-weil-pbc-spectral-limit-cohomology-map)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- The cohomology map of an `f`-map, computed by pullback followed by its adjoint.
The final restriction identifies the inverse image of the terminal open with the terminal
open. The family `c` is normalized by `SiteCohomologyFamily.IsPullback` in the theorem below.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 0A37
(blueprint: def-weil-pbc-spectral-limit-cohomology-map). -/
noncomputable def spectralLimitCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    {F : Y.Sheaf AddCommGrpCat.{u}} {G : X.Sheaf AddCommGrpCat.{u}}
    (α : F ⟶ (pushforward AddCommGrpCat.{u} f).obj G) (q : ℕ) :
    CategoryTheory.Sheaf.H' F q ⊤ ⟶ CategoryTheory.Sheaf.H' G q ⊤ :=
  c q ⊤ F ≫
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q).map
      ((sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).homEquiv F G |>.symm α))).app
      (op ((Opens.map f).obj ⊤)) ≫
    (CategoryTheory.Sheaf.cohomologyPresheaf G q).map
      (eqToHom (congrArg op (Opens.map_top f)))


end TopCat.Sheaf
