/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque

/-!
# Sheaf cohomology commutes with filtered colimits on a noetherian space

Let `X` be a noetherian topological space. Every open subset of `X` is quasi-compact, so a
filtered colimit of abelian sheaves on `X` is computed sectionwise, and sheaf cohomology
`Hⁿ(X, -)` commutes with filtered colimits
(`TopCat.Sheaf.preservesColimitsOfShape_functorH`, blueprint
`lem-sc-zariski-filtered-cohomology`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}} [NoetherianSpace X]

/-- Blueprint `lem-sc-zariski-filtered-cohomology`: Filtered colimits on a Noetherian Zariski
site.

On a noetherian topological space `X` (for instance the underlying space of a noetherian
scheme), sheaf cohomology commutes with filtered colimits of abelian sheaves:
`colimᵢ Hⁿ(X, Fᵢ) ≅ Hⁿ(X, colimᵢ Fᵢ)` for every `n`. -/
theorem preservesColimitsOfShape_functorH (J : Type u) [SmallCategory J] [IsFiltered J]
    (n : ℕ) :
    PreservesColimitsOfShape J (Sheaf.functorH.{u} (Opens.grothendieckTopology X) n) :=
  sorry

end TopCat.Sheaf
