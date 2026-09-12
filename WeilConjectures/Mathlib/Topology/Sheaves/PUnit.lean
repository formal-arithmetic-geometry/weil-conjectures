/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Topology.Sheaves.PUnit

/-!
# Presheaves of modules on a space with at most one point

`TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete` says that on a space with the indiscrete
topology, a presheaf is a sheaf as soon as its sections over the empty open subset form a
terminal object. On a space `X` with at most one point this applies to every presheaf of modules
over a sheaf of commutative rings `R`: the sections of `R` over the empty open subset form the
zero ring, hence the sections of the presheaf of modules form the zero module.

## Main declarations

- `PresheafOfModules.isSheaf_of_subsingleton`: on a space with at most one point, every presheaf
  of modules over a sheaf of commutative rings is a sheaf.

-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace PresheafOfModules

/-- **On a topological space with at most one point, every presheaf of modules over a sheaf of
commutative rings is a sheaf**: the only open subsets are `⊥` and `⊤`, and the sections over `⊥`
form the zero module, because the sections of `R` over `⊥` form the zero ring. -/
theorem isSheaf_of_subsingleton {X : TopCat.{u}} [Subsingleton X]
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    TopCat.Presheaf.IsSheaf (X := X) P.presheaf := by
  refine TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete (IndiscreteTopology.eq_top _) _ ?_
  have : Subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat.{u}).obj (op ⊥)) :=
    CommRingCat.subsingleton_of_isTerminal R.isTerminalOfEmpty
  have : Subsingleton (P.presheaf.obj (op ⊥)) :=
    Module.subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat.{u}).obj (op ⊥)) _
  exact (AddCommGrpCat.isZero_of_subsingleton _).isTerminal

end PresheafOfModules
